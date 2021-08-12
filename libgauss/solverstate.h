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
#include <unordered_set>
#include <clingo.h>
#include <cstdlib>
#include "solvertypesmini.h"
#include "gausswatched.h"
#include "Vec.h"
#include "chrono"
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
    vector<bool> in_xor;
    vec<uint32_t> decision_level_offset;
    vec<clingo_literal_t> local_trail;
    uint32_t sum_gauss_called;
    uint32_t sum_gauss_confl;
    uint32_t sum_gauss_prop;
    uint32_t sum_gauss_unit_truths;
    uint32_t sum_initEnGauss;
    uint32_t sum_initUnit;
    uint32_t sum_Enconflict;
    uint32_t sum_Enpropagate;
    uint32_t sum_Elimination_Col;
    uint32_t sum_Enunit;
    uint32_t sum_EnGauss;
    bool is_total_assignment;
    uint32_t last_trail_level;
    uint32_t backtrack_level;
    uint32_t last_trail_size;
    clingo_propagate_control_t* cpc = NULL;
    clingo_propagate_init_t* cpi = NULL;
    SolverState(uint32_t _vars, clingo_propagate_init_t* _cpi, std::unordered_set<clingo_literal_t> sol_literals)
    {
        ok = true;
        decision_level = 0;
        num_of_vars = _vars;
        assigns.clear();
        assigns.insert(assigns.end(), num_of_vars + 1, l_Undef);
        in_xor.clear();
        in_xor.assign(num_of_vars, false);
        for (auto start_literal = sol_literals.begin(), end_literal = sol_literals.end(); start_literal != end_literal ; start_literal++) {
            in_xor[*start_literal] = true;
        }
        last_trail_size = 0;
        last_trail_level = 0;
        gwatches.resize(2 * num_of_vars + 1);
        literal = sol_literals;
        clearGaussStatistics();
        decision_level_literal.clear();
        local_trail.clear();
        decision_level_offset.clear();
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
            backtrack_level = decision_level;
            // max_level = decision_level_literal.size();
        }
        else if (decision_level > decision_level_literal.size()) {
            state = dret::FORWARD;
        }
        for (uint32_t level = 0; level <= max_level; level++) {
            clingo_assignment_decision(values, level, &decision_literal);
            if (decision_level_literal.size() > level) {
                if (decision_level_literal[level] != decision_literal) {
                    if (state == dret::UNCHANGED) {
                        backtrack_level = level;
                    }
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
        // problem.time_in_back += (duration_cast<microseconds>(stop - start).count() / pow(10, 6));

        return state;
    }
    dret get_assignment(clingo_propagate_control_t *control, PackedRow* cols_vals, PackedRow* cols_unset, vector<uint32_t> var_to_col)
    {
        auto start = high_resolution_clock::now();
        cpc = control;
        dret is_backtracked = has_backtracked();
        const clingo_assignment_t *values = clingo_propagate_control_assignment(control);
        is_total_assignment = clingo_assignment_is_total(values);
        // decision_level = clingo_assignment_decision_level(values);
        clingo_truth_value_t value;
        #ifdef ASSIGNS_ENABLE
        assigns.assign(nVars(), l_Undef);
        #endif
        clingo_literal_t lit;
        uint32_t col, new_trail_size;
        clingo_assignment_trail_size(values, &new_trail_size);
        if (is_backtracked == dret::UNCHANGED) {
            uint32_t trail_at;
            assert(new_trail_size - last_trail_size >= 0);
            for (trail_at = last_trail_size; trail_at < new_trail_size; trail_at++) {
                clingo_assignment_trail_at(values, trail_at, &lit);
                if (abs(lit) <= in_xor.size() && in_xor[abs(lit)]) {
                    col = var_to_col[abs(lit)];
                    if (col == std::numeric_limits<uint32_t>::max()) 
                        continue; 
                    local_trail.push(lit);
                    if (lit > 0) {
                        cols_unset->clearBit(col);
                        cols_vals->setBit(col);
                    }
                    else if (lit < 0) {
                        cols_unset->clearBit(col);
                    }
                }
            }
            if (decision_level == 0 && decision_level_offset.size() == 0) {
                decision_level_offset.push(0);
            }
            decision_level_offset[decision_level] = local_trail.size();
        }
        else if (is_backtracked == dret::FORWARD) {
            uint32_t trail_at;
            uint32_t start_level = last_trail_level, offset_end, offset_start, literal_inserted;
            assert(decision_level > last_trail_level);
            for (auto level_at = start_level ; level_at <= decision_level; level_at++) {
                clingo_assignment_trail_begin(values, level_at, &offset_start);
                clingo_assignment_trail_end(values, level_at, &offset_end);
                if (level_at == last_trail_level) {
                    offset_start = last_trail_size;
                }
                else {
                    // it is level_at'th level
                    assert(decision_level_offset.size() >= level_at);
                    if (decision_level_offset.size() == level_at) {
                        decision_level_offset.push(local_trail.size());
                    }
                    assert(offset_start < offset_end);
                }
                for (trail_at = offset_start; trail_at < offset_end; trail_at++) {
                    clingo_assignment_trail_at(values, trail_at, &lit);
                    if (abs(lit) <= in_xor.size() && in_xor[abs(lit)]) {
                        col = var_to_col[abs(lit)];
                        if (col == std::numeric_limits<uint32_t>::max()) 
                            continue; 
                        local_trail.push(lit);
                        if (lit > 0) {
                            cols_unset->clearBit(col);
                            cols_vals->setBit(col);
                        } else if (lit < 0) {
                            cols_unset->clearBit(col);
                        }
                    }
                }
                decision_level_offset[level_at] = local_trail.size(); 
            }
        }
        else {
            uint32_t trail_at;
            uint32_t start_level = backtrack_level, offset_end, offset_start;
            offset_start = decision_level_offset[backtrack_level - 1];
            offset_end = local_trail.size();
            for (trail_at = offset_start; trail_at < offset_end; trail_at++) {
                // unassigning the value
                col = var_to_col[abs(local_trail[trail_at])];
                cols_unset->setBit(col);
                cols_vals->clearBit(col);
            }
            local_trail.resize(decision_level_offset[backtrack_level - 1]);
            decision_level_offset.resize(backtrack_level);

            for (auto level_at = start_level ; level_at <= decision_level; level_at++) {
                clingo_assignment_trail_begin(values, level_at, &offset_start);
                clingo_assignment_trail_end(values, level_at, &offset_end);
                // if (level_at == last_trail_level) {
                //     offset_start = last_trail_size;
                // }
                // else {
                    // it is level_at'th level
                    assert(decision_level_offset.size() >= level_at);
                    if (decision_level_offset.size() == level_at) {
                        decision_level_offset.push(local_trail.size());
                    }
                    assert(offset_start < offset_end);
                // }
                for (trail_at = offset_start; trail_at < offset_end; trail_at++) {
                    clingo_assignment_trail_at(values, trail_at, &lit);
                    if (abs(lit) <= in_xor.size() && in_xor[abs(lit)]) {
                        col = var_to_col[abs(lit)];
                        if (col == std::numeric_limits<uint32_t>::max()) 
                            continue; 
                        local_trail.push(lit);
                        if (lit > 0) {
                            cols_unset->clearBit(col);
                            cols_vals->setBit(col);
                        } else if (lit < 0) {
                            cols_unset->clearBit(col);
                        }
                    }
                }
                decision_level_offset[level_at] = local_trail.size(); 
            }
        }
        auto stop = high_resolution_clock::now();
        problem.clingo_assignment_time += duration_cast<microseconds>(stop - start).count() / pow(10, 6);
        problem.clingo_assignment_called++;
        clingo_assignment_trail_size(values, &last_trail_size);
        last_trail_level = decision_level;
        return is_backtracked;
    }
    void clearGaussStatistics()
    {
        sum_Enconflict = 0;
        sum_EnGauss = 0;
        sum_gauss_called = 0;
        sum_gauss_confl = 0;
        sum_gauss_prop = 0;
        sum_gauss_unit_truths = 0;
        sum_initEnGauss = 0;
        sum_Elimination_Col = 0;
        sum_initUnit = 0;
        sum_Enpropagate = 0;
        sum_Enunit = 0;
    }
    void printStatistics() {
        cout << "sum_Enconflict:\t" <<  sum_Enconflict << endl;
        cout << "sum_EnGauss:\t" << sum_EnGauss << endl;
        cout << "sum_initEnGauss:\t" << sum_initEnGauss << endl;
        cout << "sum_initUnit:\t" << sum_initUnit << endl;
        cout << "sum_Enpropagate:\t" << sum_Enpropagate << endl;
        cout << "sum_Enunit:\t" << sum_Enunit << endl;
    }
    void add_watch_literal(uint32_t lit) {
        if (gwatches[lit].size() > 1) return;
        #ifdef DEBUG
        assert(gwatches[lit].size() == 1);
        #endif
        if (cpc) {
            clingo_propagate_control_add_watch(cpc, (clingo_literal_t) lit);
            clingo_propagate_control_add_watch(cpc, (clingo_literal_t) -lit);
        }
        else {
            assert(cpi);
            clingo_propagate_init_add_watch(cpi, (clingo_literal_t) lit);
            clingo_propagate_init_add_watch(cpi, (clingo_literal_t) -lit);
        }
    }
    void remove_watch_literal(uint32_t lit) {
        if (!cpc)
            return; 
        if (gwatches[lit].size() >= 1) return;
        clingo_propagate_control_remove_watch(cpc, (clingo_literal_t) lit);
        clingo_propagate_control_remove_watch(cpc, (clingo_literal_t) -lit);
    }
    bool is_assignment_conflicting(clingo_propagate_control_t *control) {
        const clingo_assignment_t *values = clingo_propagate_control_assignment(control);
        return clingo_assignment_has_conflict(values);
    }
    bool add_clause(vector<clingo_literal_t> clause, bool is_conflict_clause = false) {
        auto start = high_resolution_clock::now();
        auto last_literal = literal.end();
        problem.clingo_add_clause_called++;
        assert(cpc);
        size_t length = clause.size();
        bool result;
        clingo_literal_t* new_clause;
        new_clause = clause.data();
        // clingo_literal_t* new_clause = (clingo_literal_t *)malloc (length * sizeof(clingo_literal_t));
        // auto itr = clause.begin();
        // u_int32_t index = 0;
        // clingo_literal_t insert_lit, test_lit;
        // for (auto itr_end = clause.end(); itr != itr_end; itr++) {
        //     test_lit = (*itr).var();
        //     #ifdef DEBUG
        //     assert(literal.find(test_lit) != last_literal);
        //     assert(literal.find(test_lit) != literal.end());
        //     if (index == 0 && !is_conflict_clause) {
        //         assert(assigns[test_lit] == l_Undef);
        //     }
        //     else if ((*itr).sign())
        //     {
        //         assert(assigns[test_lit] == l_True);
        //     }
        //     else
        //     {
        //         assert(assigns[test_lit] == l_False);
        //     }
        //     #endif
        //     insert_lit = (clingo_literal_t)((*itr).sign()) ? (-(*itr).var()) : ((*itr).var());
        //     new_clause[index++] = insert_lit;
        // }
        // assert(index == length);
        // bool is_conflict = is_assignment_conflicting(cpc); 	
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
            problem.clingo_add_clause_time += duration_cast<microseconds>(stop - start).count() / pow(10, 6);
            return false;	
        }	
        if (!clingo_propagate_control_propagate(cpc, &result))	
        {	
            cout << "Can't propagate clause";	
        }	
        if (!result) {	
            auto stop = high_resolution_clock::now();
            problem.clingo_add_clause_time += duration_cast<microseconds>(stop - start).count() / pow(10, 6);
            return false;	
        }
        // free(new_clause);
        auto stop = high_resolution_clock::now();
        problem.clingo_add_clause_time += duration_cast<microseconds>(stop - start).count() / pow(10, 6);
        assert(result);
        return true;
    }
    bool add_initial_clause(vector<clingo_literal_t> clause) {
        assert(cpi);
        assert(clause.size() == 1);
        clingo_literal_t* new_clause = (clingo_literal_t *)malloc (sizeof(clingo_literal_t));
        new_clause[0] = clause[0];
        bool result;
        // add the clause
        if (!clingo_propagate_init_add_clause(cpi, new_clause, 1, &result)) { return false; }
        if (!result) { return false; }
        // propagate it
        if (!clingo_propagate_init_propagate(cpi, &result)) { return false; }
        if (!result) { return false; }
        const clingo_assignment_t *values = clingo_propagate_init_assignment(cpi);
        auto start_literal = literal.begin(); 
        assigns.assign(nVars(), l_Undef);
        clingo_truth_value_t value;
        for (auto end_literal = literal.end(); start_literal != end_literal ; start_literal++)
        {
            clingo_assignment_truth_value(values, *start_literal, &value);
            switch (value)
            {
                case clingo_truth_value_true:
                    assigns[*start_literal] = l_True;
                    break;
                case clingo_truth_value_false:
                    assigns[*start_literal] = l_False;
                    break;
                default:
                    break;
            }
        }
        return true;
    }
    bool make_unsat() {
        assert(cpi);
        clingo_literal_t* new_clause = (clingo_literal_t *)malloc (sizeof(clingo_literal_t));
        // if (clause[0].sign()) {
        //     new_clause[0] = -clause[0].var();
        // }
        // else {
        //     new_clause[0] = clause[0].var();
        // }
        bool result;
        // add the clause
        if (!clingo_propagate_init_add_clause(cpi, new_clause, 0, &result)) { return false; }
        if (!result) { return false; }
        // propagate it
        if (!clingo_propagate_init_propagate(cpi, &result)) { return false; }
        if (!result) { return false; }
    }
};

// }


#endif //SOLVERSTATE_H_
