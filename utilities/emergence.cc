#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include <string>
#include <iostream>
#include <fstream>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <cctype>
#include <ctime>
#include <limits>
#include "types.hh"
#include "utilities.hh"
#include "cuddObj.hh"

#define MAXINISTATES 100
#define MAXTRANSITIONS 100
#define MAXSTACKDEPTH 100

extern vector<string *> *string_table;
extern vector<bool_expression *> *logic_expression_table;
extern vector<bool_expression *> *logic_expression_table1;
extern vector<variable *> *variable_table;
extern map<string, basic_agent *> *is_agents;
extern vector<basic_agent *> *agents;
extern map<string, bool_expression *> *is_evaluation;
extern bool_expression *is_istates;
extern map<string, set<string> > *is_groups;
extern vector<modal_formula> *is_formulae;
extern vector<fairness_expression *> *is_fairness;
extern map < string, int > options;
extern Cudd_ReorderingType REORDERING;

extern BDD append_variable_BDDs(Cudd *bddmgr, vector<BDD> *v, BDD a);
extern bool is_valid_state(BDD state, vector<BDD> v);
extern bool is_valid_action(BDD state, vector<BDD> a);
extern bool find_same_state(map<string, int> *statehash, string state);
extern void print_action_1(BDD state, vector<BDD> a);
extern string state_to_str(BDD state, vector<BDD> v);
extern string nometa_state_to_str(BDD state, vector<BDD> v);
extern pair<vector<int>, vector<int>> calculate_out_ins(BDD state, vector<BDD> v);
extern void print_state(BDD state, vector<BDD> v);
extern void print_action(BDD state, vector<BDD> a);
extern BDD Exists(Cudd *bddmgr, vector<BDD>* v, BDD x);
extern map<string, map<string, vector<BDD*>* >* >* integer_variable_BDDs(Cudd * bddmgr, vector<BDD> * v);
extern void clear_integer_BDDs(map<string, map<string, vector<BDD*>* >* >* int_vars);
extern BDD complete_integer_BDDs(Cudd * bddmgr, vector<BDD> * v, BDD a, map<string, map<string, vector<BDD*>* >* >* int_vars);

// returns next valid minterm and inserts corresponding string into statehash 
BDD get_next_minterm(BDD& states, set<string>& statehash, bdd_parameters* para) {
  while (states != para->bddmgr->bddZero()) {
    auto next = states.PickOneMinterm(*para->v);
    states = states - next;
    if (is_valid_state(next, *para->v)) {
      string state = state_to_str(next, *para->v);
      auto result = statehash.insert(state);
      bool new_element_inserted = result.second;
      if (new_element_inserted) {
        return next;
      }
    }
  }

  return para->bddmgr->bddZero();
}

// checks for cycles of n repetitions in the stack
bool has_cycles(const vector<string>& states, int num_cycles) {
  int num_states = states.size();
  int max_cycle_size = (states.size() - 1) / num_cycles; 

  for (int cycle_size = 1; cycle_size <= max_cycle_size; ++cycle_size) {
    bool equal = true;

    for (int offset = 0; offset < cycle_size; ++offset) {
      const string& first_cycle_elem = states[num_states - offset - 2];

      for (int index = 1; index < num_cycles; ++index) {
        if (first_cycle_elem != states[num_states - index * cycle_size - offset - 2]) {
          equal = false;
          break;
        }
      }

      if (!equal) {
        break;
      }
    }

    if (states[num_states - 1] != states[num_states - cycle_size - 1]) {
      equal = false;
    }

    if (equal) {
      return true;
    }
  }

  return false;
}

int find_threshold(int temporaldepth, const BDD& initial_state,
                    bdd_parameters* para) {
  
  int currentthreshold = 0;
  int maxthreshold = 0;

  vector<BDD> stack = {initial_state};
    
  vector<string> prevstates;
  vector<set<string>> prevstatehashes = {set<string>()};

  auto [initialouts, initialins] = calculate_out_ins(initial_state, *para->v);
  vector<vector<int>> previns = {initialins};
  vector<vector<int>> prevouts = {initialouts};

  vector<int> prev_threshold_components = {0};

  bool check = true;
  while (!stack.empty()) {
    auto& current = stack.back();
    if (current == para->bddmgr->bddZero()) {
      stack.pop_back();
      if (!prevstates.empty()) {
        prevstates.pop_back();
      }
      prevstatehashes.pop_back();
      prevouts.pop_back();
      previns.pop_back();
      currentthreshold -= prev_threshold_components.back();
      prev_threshold_components.pop_back();
      continue;
    }

    auto& currentstatehash = prevstatehashes.back();
    auto next_state = get_next_minterm(current, currentstatehash, para);

    if (next_state == para->bddmgr->bddZero()) {
      stack.pop_back();
      prevstatehashes.pop_back();
      prevouts.pop_back();
      previns.pop_back();
      currentthreshold -= prev_threshold_components.back();
      prev_threshold_components.pop_back();
      if (!prevstates.empty()) {
        prevstates.pop_back();
      }
      continue;
    }

    auto state_string = nometa_state_to_str(next_state, *para->v);

    prevstates.emplace_back(std::move(state_string));

    if (has_cycles(prevstates, temporaldepth + 1)) {
      prevstates.pop_back();
      continue;
    }

    auto [out, in] = calculate_out_ins(next_state, *para->v);

    prevouts.emplace_back(std::move(out));
    previns.emplace_back(std::move(in));

    if (prevouts.size() >= 2) {
      int current_threshold_component = 0;
      vector<int>& out = prevouts.back();
      vector<int>& in = previns[prevouts.size() - 2];
      for (size_t i = 0; i < out.size(); ++i) {
        current_threshold_component += std::max(0, out[i] - in[i]);
      }
      prev_threshold_components.emplace_back(current_threshold_component);
      currentthreshold += current_threshold_component;
      maxthreshold = std::max(currentthreshold, maxthreshold);
    }

    auto newstates = next_state; 
    for (auto& transition : *para->vRT) {
      newstates *= transition;
    }

    newstates = Exists(para->bddmgr, para->v, newstates);
    newstates = newstates.SwapVariables(*para->v, *para->pv);
    newstates = Exists(para->bddmgr, para->a, newstates);

    stack.emplace_back(std::move(newstates));
    prevstatehashes.emplace_back(set<string>());
  }

  return maxthreshold;
}

void emergence(void *ptr) {
  cout << "Finding Emergence Threshold..." << endl;

  bdd_parameters *para;
  para = (bdd_parameters *)ptr;
  Cudd* bddmgr = para->bddmgr; 
  vector<BDD> *v = para->v;
  vector<ADD> *addv = para->addv;
  vector<BDD> *pv = para->pv;
  vector<ADD> *addpv = para->addpv;
  vector<BDD> *a = para->a;
  vector<BDD> *vevol = para->vevol;
  vector<BDD> *vprot = para->vprot;
  vector<BDD> *vRT = para->vRT;
  BDD in_st;

  Cudd_AutodynEnable(bddmgr->getManager(), REORDERING);
  in_st = is_istates->encode_bdd_flat(para, bddmgr->bddOne());
  in_st = append_variable_BDDs(bddmgr, v, in_st);
  if (in_st==bddmgr->bddZero()) {
    cout << "No initial state. Check your model!" << endl;
    return;
  }

  map<string, map<string, vector<BDD*>* >* >* int_vars = integer_variable_BDDs(bddmgr, v);

  for (unsigned int i=0; i<agents->size(); i++) {
    vprot->push_back((*agents)[i]->encode_protocol(para));
    if(options["smv"] == 0)
      vevol->push_back((*agents)[i]->encode_evolution(para));
    else
      vevol->push_back((*agents)[i]->encode_evolution_smv(para));
    vRT->push_back((*vprot)[i] * (*vevol)[i]);
  }

  REORDERING = options["dyn"] == 1 ? CUDD_REORDER_GROUP_SIFT : CUDD_REORDER_SIFT; 
  Cudd_AutodynEnable(bddmgr->getManager(), REORDERING);  
  vector<BDD> inistates;
  int count=0;
  BDD is = in_st;
  map<string, int> statehash;

  cout << "Generating Computation Tree Roots..." << endl;
  while (count<MAXINISTATES && is != bddmgr->bddZero()) { 
  //while (count<1 && is != bddmgr->bddZero()) {
    if(count >= inistates.size())
      inistates.push_back(is.PickOneMinterm(*v));
    else
      inistates[count] = is.PickOneMinterm(*v);
    is = is - inistates[count];
    if (is_valid_state(inistates[count], *v)) {
      string state = nometa_state_to_str(inistates[count], *v);
      if(!find_same_state(&statehash, state)) {
        statehash[state] = 1;
        count++;
      } else {
        //cout << "same state " << count << endl;
      }
    } else {
      //cout << "invalid" << endl;
    }
  }

  if (count==MAXINISTATES && is != bddmgr->bddZero())
    std::cout << "There are too many initial states. Please specify more initial values."
          << std::endl;

  int temporaldepth = options["temporaldepth"];
  int maxdepth = 0;
  cout << "Traversing Computation Trees..." << endl;
  for (auto& inistate : inistates) {
    int current_maxdepth = find_threshold(temporaldepth, inistate, para);
    maxdepth = std::max(current_maxdepth, maxdepth);
  }

  cout << "The emergence threshold of the model is " << maxdepth << endl;

  clear_integer_BDDs(int_vars);
}
