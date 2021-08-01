// {{{ MIT License

// Copyright 2019 Mahi XYZ

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// IN THE SOFTWARE.

// }}}


#ifndef SOLVERSTATE_H_
#define SOLVERSTATE_H_
#include <vector>
#include <chrono>
#include <unordered_set>
#include <clingo.h>
#include <cstdlib>
#include "solvertypesmini.h"
#include "gausswatched.h"
#include "Vec.h"
#include "utility.h"
using namespace std::chrono;
extern Configuration problem;
// namespace CMSat {
class SolverState
{
private:
    /* data */
public:
    uint32_t decision_level;
    bool ok;
    size_t num_of_vars;
    vector<lbool> assigns;
    std::unordered_set<clingo_literal_t> literal;
    vec<vec<GaussWatched>> gwatches;
    vec<clingo_literal_t> decision_level_literal;
    uint32_t sum_gauss_called;
    uint32_t sum_gauss_confl;
    uint32_t sum_gauss_prop;
    uint32_t sum_gauss_unit_truths;
    uint32_t sum_initEnGauss;
    uint32_t sum_initUnit;
    uint32_t sum_Enconflict_propagate;
    uint32_t sum_Enconflict_check;
    uint32_t sum_Elimination_Col;
    uint32_t sum_Enpropagate_propagate;
    uint32_t sum_Enpropagate_check;
    uint32_t sum_Enunit;
    uint32_t sum_EnGauss;
    uint32_t find_truth_ret_satisfied_precheck;
    uint32_t find_truth_ret_unresolved_precheck;
    uint32_t find_truth_ret_unnecessary_precheck;
    bool total_assignment;
    clingo_propagate_control_t* cpc = NULL;
    clingo_propagate_init_t* cpi = NULL;
    SolverState(uint32_t _vars, clingo_propagate_init_t* _cpi, std::unordered_set<clingo_literal_t> sol_literals)
    {
        ok = true;
        decision_level = 0;
        num_of_vars = _vars;
        assigns.clear();
        assigns.insert(assigns.end(), num_of_vars + 1, l_Undef);
        gwatches.resize(2 * num_of_vars + 1);
        literal = sol_literals;
        clearGaussStatistics();
        decision_level_literal.clear();
        cpi = _cpi;
    }

    ~SolverState()
    {
    }
    lbool value(const uint32_t x)
    {
        assert(literal.find(x) != literal.end());
        assert(x <= assigns.size());
        return assigns[x];
    }

    lbool value(const Lit p)
    {
        assert(literal.find(p.var()) != literal.end());
        return assigns[p.var()] ^ p.sign();
    }
    size_t nVars()
    {
        return num_of_vars + 1;
    }
    bool okay()
    {
        return ok;
    }
    uint32_t decisionLevel()
    {
        return decision_level;
    }
    dret has_backtracked() {
        auto start = high_resolution_clock::now();
        dret state = dret::UNCHANGED;
        clingo_literal_t decision_literal;
        const clingo_assignment_t *values = clingo_propagate_control_assignment(cpc);
        decision_level = clingo_assignment_decision_level(values);
        uint32_t max_level = decision_level;
        if (decision_level < decision_level_literal.size()) {
            state = dret::BACKTRACK;
            // max_level = decision_level_literal.size();
        }
        else if (decision_level > decision_level_literal.size()) {
            state = dret::FORWARD;
        }
        for (uint32_t level = 0; level <= max_level; level++) {
            clingo_assignment_decision(values, level, &decision_literal);
            if (decision_level_literal.size() > level) {
                if (decision_level_literal[level] != decision_literal) {
                    state = dret::BACKTRACK;
                } 
                decision_level_literal[level] = decision_literal;
            }
            else {
                decision_level_literal.push(decision_literal);
            }
        }
        decision_level_literal.resize(decision_level);
        auto stop = high_resolution_clock::now();
        problem.time_in_back += (duration_cast<microseconds>(stop - start).count() / pow(10, 6));

        return state;
    }
    dret get_assignment(clingo_propagate_control_t *control, PackedRow* cols_vals, PackedRow* cols_unset, vector<uint32_t> var_to_col)
    {
        auto start = high_resolution_clock::now();
        cpc = control;
        dret is_backtracked = has_backtracked();
        const clingo_assignment_t *values = clingo_propagate_control_assignment(control);
        total_assignment = clingo_assignment_is_total(values);
        // assert(!clingo_assignment_has_conflict(values));
        #ifdef DEBUG
        decision_level = clingo_assignment_decision_level(values);
        #endif
        clingo_truth_value_t value;
        bool true_value, false_value;
        // vector<lbool> prev_assigns;
        // prev_assigns = assigns;
        // assigns.assign(nVars(), l_Undef);
        auto start_literal = literal.begin(); 
        cols_vals->setZero();
        cols_unset->setOne();
        for (auto end_literal = literal.end(); start_literal != end_literal ; start_literal++)
        {
            #ifdef DEBUG
            assert(clingo_assignment_has_literal(values, *start_literal));
            #endif
            clingo_assignment_truth_value(values, *start_literal, &value);
            #ifdef DEBUG
            clingo_assignment_is_true(values, *start_literal, &true_value);
            clingo_assignment_is_false(values, *start_literal, &false_value);
            #endif
            uint32_t col = var_to_col[*start_literal];
            switch (value)
            {
                case clingo_truth_value_true:
                    #ifdef PREVIOUS_ASSIGN
                    assigns[*start_literal] = l_True;
                    #endif
                    cols_unset->clearBit(col);
                    cols_vals->setBit(col);
                    // assert((*cols_vals)[col] == 1);
                    // assert((*cols_unset)[col] == 0);
                    // if (prev_assigns[*start_literal] == l_False) {
                    //     is_backtracked = true;
                    // }
                    #ifdef DEBUG
                    assert(true_value);
                    #endif
                    break;
                case clingo_truth_value_false:
                    #ifdef PREVIOUS_ASSIGN
                    assigns[*start_literal] = l_False;
                    #endif
                    cols_unset->clearBit(col);
                    // assert((*cols_vals)[col] == 0);
                    // assert((*cols_unset)[col] == 0);
                    // if (prev_assigns[*start_literal] == l_True) {
                    //     is_backtracked = true;
                    // }
                    #ifdef DEBUG
                    assert(false_value);
                    #endif
                    break;
                default:
                    // assert((*cols_unset)[col] == 1);
                    #ifdef PREVIOUS_ASSIGN
                    assigns[*start_literal] = l_Undef;
                    #endif
                    // if (prev_assigns[*start_literal] != l_Undef) {
                    //     is_backtracked = true;
                    // }
                    break;
            }
        }
        auto stop = high_resolution_clock::now();
        problem.time_in_assignment += (duration_cast<microseconds>(stop - start).count() / pow(10, 6));
        problem.assignment_called++;
        return is_backtracked;
    }
    void clearGaussStatistics()
    {
        sum_Enconflict_propagate = 0;
        sum_Enconflict_check = 0;
        sum_EnGauss = 0;
        sum_gauss_called = 0;
        sum_gauss_confl = 0;
        sum_gauss_prop = 0;
        sum_gauss_unit_truths = 0;
        sum_initEnGauss = 0;
        sum_initUnit = 0;
        sum_Enpropagate_propagate = 0;
        sum_Enpropagate_check = 0;
        sum_Enunit = 0;
        sum_Elimination_Col = 0;
        find_truth_ret_satisfied_precheck = 0;
        find_truth_ret_unresolved_precheck = 0;
        find_truth_ret_unnecessary_precheck = 0;
    }
    void printStatistics() {
        cout << "sum_Enconflict_Propagate:\t" <<  sum_Enconflict_propagate << endl;
        cout << "sum_Enconflict_Check:\t" <<  sum_Enconflict_check << endl;
        cout << "sum_EnGauss:\t" << sum_EnGauss << endl;
        cout << "sum_initEnGauss:\t" << sum_initEnGauss << endl;
        cout << "sum_initUnit:\t" << sum_initUnit << endl;
        cout << "sum_Enpropagate_propagate:\t" << sum_Enpropagate_propagate << endl;
        cout << "sum_Enpropagate_check:\t" << sum_Enpropagate_check << endl;
        cout << "sum_Enunit:\t" << sum_Enunit << endl;
        cout << "sum_Elimination_Col:\t" << sum_Elimination_Col << endl;
        cout << "find_truth_ret_satisfied_precheck:\t" << find_truth_ret_satisfied_precheck << endl;
        cout << "find_truth_ret_unresolved_precheck:\t" << find_truth_ret_unresolved_precheck << endl;
        cout << "find_truth_ret_unnecessary_precheck:\t" << find_truth_ret_unnecessary_precheck << endl;
    }
    void add_watch_literal(uint32_t lit) {
        if (gwatches[lit].size() > 1) {
            // assert(clingo_propagate_control_has_watch(cpc, lit));
            return;
        };
        // cout << lit << endl;
        assert(gwatches[lit].size() == 1);
        auto start = high_resolution_clock::now();
        if (cpc) {
            clingo_propagate_control_add_watch(cpc, (clingo_literal_t) lit);
            clingo_propagate_control_add_watch(cpc, (clingo_literal_t) -lit);
        }
        else {
            assert(cpi);
            clingo_propagate_init_add_watch(cpi, (clingo_literal_t) lit);
            clingo_propagate_init_add_watch(cpi, (clingo_literal_t) -lit);
        }
        problem.watch_called++;
        auto stop = high_resolution_clock::now();
        problem.time_in_watch += (duration_cast<microseconds>(stop - start).count() / pow(10, 6));
    }
    void remove_watch_literal(uint32_t lit) {
        if (!cpc)
            return; 
        // cout << lit << endl;
        // assert(clingo_propagate_control_has_watch(cpc, (clingo_literal_t) lit));
        if (gwatches[lit].size() >= 1) return;
        auto start = high_resolution_clock::now();
        clingo_propagate_control_remove_watch(cpc, (clingo_literal_t) lit);
        clingo_propagate_control_remove_watch(cpc, (clingo_literal_t) -lit);
        problem.watch_called++;
        auto stop = high_resolution_clock::now();
        problem.time_in_watch += (duration_cast<microseconds>(stop - start).count() / pow(10, 6));
    }
    bool is_assignment_conflicting(clingo_propagate_control_t *control) {
        const clingo_assignment_t *values = clingo_propagate_control_assignment(control);
        return clingo_assignment_has_conflict(values);
    }
    bool is_conflicting(vector<clingo_literal_t> clause, int is_conflict_clause) {
        auto itr = clause.begin() + is_conflict_clause;
        clingo_literal_t insert_lit, test_lit;
        bool result;
        const clingo_assignment_t *values = clingo_propagate_control_assignment(cpc);
        for (auto itr_end = clause.end(); itr != itr_end; itr++) { 
            test_lit = *itr;
            clingo_assignment_is_true(values, test_lit, &result);
            if (*itr < 0) {
                if (!result) 
                    return false;
            } 
            else {
                if (result) 
                    return false;
            }
        }
        return true;
    }
    bool is_assignments_equal(const clingo_assignment_t* assign1, const clingo_assignment_t* assign2) {
        auto start_literal = literal.begin(); 
        clingo_truth_value_t value1, value2;
        for (auto end_literal = literal.end(); start_literal != end_literal ; start_literal++)
        {
            assert(clingo_assignment_has_literal(assign1, *start_literal));
            clingo_assignment_truth_value(assign1, *start_literal, &value1);
            assert(clingo_assignment_has_literal(assign2, *start_literal));
            clingo_assignment_truth_value(assign2, *start_literal, &value2);
            if (value1 != value2) {
                return false;
            }
        }
        return true;
    }
    bool add_clause(vector<clingo_literal_t> clause, bool is_conflict_clause = false) {
        auto start = high_resolution_clock::now();
        problem.add_clause_called += 1;
        auto last_literal = literal.end();
        assert(cpc);
        size_t length = clause.size();
        bool result;
        clingo_truth_value_t value;
        // clingo_literal_t* new_clause = (clingo_literal_t *)malloc (length * sizeof(clingo_literal_t));
        // auto itr = clause.begin();
        u_int32_t index = 0;
        clingo_literal_t insert_lit, test_lit;
        clingo_symbol_t symbol;
        #ifdef DEBUG_MODE
        if (is_conflict_clause) {
            cout << "Conflict clause added : [ "; 
        }
        #endif
        // cout << " :- ";
        // const clingo_assignment_t *values1 = clingo_propagate_control_assignment(cpc);
        clingo_literal_t* new_clause; 
        new_clause = clause.data();
        // for (auto itr_end = clause.end(); itr != itr_end; itr++) {
        //     test_lit = *itr;
            #ifdef DEBUG
            assert(literal.find(test_lit) != last_literal);
            assert(literal.find(test_lit) != literal.end());
            #endif
            // clingo_assignment_truth_value(values, test_lit, &value);
            // if (index == 0 && !is_conflict_clause) {
            //     assert(assigns[test_lit] == l_Undef);
            //     assert(value == clingo_truth_value_free);
            // }
            // else if ((*itr).sign())
            // {
            //     assert(assigns[test_lit] == l_True);
            //     assert(value == clingo_truth_value_true);
            // }
            // else
            // {
            //     assert(assigns[test_lit] == l_False);
            //     assert(value == clingo_truth_value_false);
            // }
            // std::unordered_map<clingo_literal_t, clingo_symbol_t>::iterator symbol_itr = problem.literal_atom_map.find(test_lit);
            // // cout << symbol_itr->second;
            // std::unordered_map<clingo_symbol_t, string>::iterator atom_itr = problem.atom_symbol_map.find(symbol_itr->second);
            // if ((*itr).sign()) {
            //     cout << atom_itr->second;
            // }
            // else {
            //     cout << " not "<< atom_itr->second;
            // }
            // if (itr != itr_end - 1) {
            //     cout << ",";
            // }
            // else {
            //     cout << ".";
            // }
            // insert_lit = *itr;
            #ifdef DEBUG_MODE
            if (is_conflict_clause) {
                cout << insert_lit << " "; 
            }
            #endif
            // new_clause[index++] = insert_lit;
        // }
        #ifdef DEBUG_MODE
        if (is_conflict_clause) {
            cout << " ]" << endl; 
        }
        #endif
        // assert(index == length);
        #ifdef DEBUG
        bool is_conflict = is_assignment_conflicting(cpc); 
        #endif
        // assert(is_conflicting(clause, !is_conflict_clause));
        if (!clingo_propagate_control_add_clause(cpc, new_clause, length, clingo_clause_type_volatile, &result))
        {
            (is_conflict_clause) ? printf("\nConflict\n") : printf("\nPropagation\n");
            
            
            // itr = clause.begin();
            // assert(assigns[(*itr).var()] == l_Undef);
            // for (auto itr_end = clause.end(); itr != itr_end; itr++)
            // {
            //     test_lit = (*itr).var();
            //     printf("%d\t", (*itr).var());
            //     assert(literal.find(test_lit) != last_literal);
            //     insert_lit = (clingo_literal_t)((*itr).sign()) ? (-(*itr).var()) : ((*itr).var());
            //     new_clause[index++] = insert_lit;
            //     printf("%d\t", insert_lit);
            // }
            cout << "\nCan't insert clause\n";
            
        }
        // const clingo_assignment_t *values2 = clingo_propagate_control_assignment(cpc);
        // assert(is_assignments_equal(values1, values2));
        if (is_conflict_clause) {
            // if(!is_conflict && is_assignment_conflicting(cpc)) {
            //     cout << "yes";
            // }
            // else if (!is_assignment_conflicting(cpc)) {
            //     assert(false);
            // }
            assert(!result);  // this is conflicting
        }
        // if (!is_conflict_clause && !clingo_propagate_control_add_clause(cpc, new_clause, length, clingo_clause_type_volatile, &result))
        // {
        //     (is_conflict_clause) ? printf("\nConflict\n") : printf("\nPropagation\n");
            
        //     cout << "\nCan't insert clause\n";
            
        // }
        if (!result) {
            auto stop = high_resolution_clock::now();
            problem.time_in_add_clause += (duration_cast<microseconds>(stop - start).count() / pow(10, 6));
            return false;
        }
        if (!clingo_propagate_control_propagate(cpc, &result))
        {
            cout << "Can't propagate clause";
        }
        if (!result) {
            auto stop = high_resolution_clock::now();
            problem.time_in_add_clause += (duration_cast<microseconds>(stop - start).count() / pow(10, 6));
            return false;
        }
        // get_assignment(cpc);
        // free(new_clause);
        assert(result);  // this is propagating
        auto stop = high_resolution_clock::now();
        problem.time_in_add_clause += (duration_cast<microseconds>(stop - start).count() / pow(10, 6));
        return true;
        // is_conflict_clause = false;
        // if it is a binary clause then add one more new clause
        // if (is_conflict_clause)
        // {
        //     assert(length == 2);
        //     new_clause[0] = -new_clause[0];
        //     new_clause[1] = -new_clause[1];
        //     if (!clingo_propagate_control_add_clause(cpc, new_clause, length, clingo_clause_type_volatile, &result))
        //     {
        //         cout << "Can't insert clause";
        //     }
        // }
    }
    bool add_initial_clause(vector<clingo_literal_t> clause) {
        assert(cpi);
        assert(clause.size() == 1);
        clingo_literal_t* new_clause = (clingo_literal_t *)malloc (sizeof(clingo_literal_t));
        new_clause[0] = clause[0];
        // if (clause[0].sign()) {
        //     new_clause[0] = -clause[0].var();
        // }
        // else {
        //     new_clause[0] = clause[0].var();
        // }
        bool result;
        // add the clause
        if (!clingo_propagate_init_add_clause(cpi, new_clause, 1, &result)) { return false; }
        if (!result) { return false; }
        // propagate it
        if (!clingo_propagate_init_propagate(cpi, &result)) { return false; }
        if (!result) { return false; }
        return true;
    }
};

// }


#endif //SOLVERSTATE_H_
