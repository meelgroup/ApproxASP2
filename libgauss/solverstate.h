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
    uint32_t sum_gauss_called;
    uint32_t sum_gauss_confl;
    uint32_t sum_gauss_prop;
    uint32_t sum_gauss_unit_truths;
    uint32_t sum_initEnGauss;
    uint32_t sum_initUnit;
    uint32_t sum_Enconflict;
    uint32_t sum_Elimination_Col;
    uint32_t sum_Enpropagate;
    uint32_t sum_Enunit;
    uint32_t sum_EnGauss;
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
    void get_assignment(clingo_propagate_control_t *control)
    {
        cpc = control;
        const clingo_assignment_t *values = clingo_propagate_control_assignment(control);
        assert(!clingo_assignment_has_conflict(values));
        decision_level = clingo_assignment_decision_level(values);
        clingo_truth_value_t value;
        bool true_value, false_value;
        assigns.assign(nVars(), l_Undef);
        auto start_literal = literal.begin(); 
        for (auto end_literal = literal.end(); start_literal != end_literal ; start_literal++)
        {
            assert(clingo_assignment_has_literal(values, *start_literal));
            clingo_assignment_truth_value(values, *start_literal, &value);
            clingo_assignment_is_true(values, *start_literal, &true_value);
            clingo_assignment_is_false(values, *start_literal, &false_value);
            switch (value)
            {
                case clingo_truth_value_true:
                    assigns[*start_literal] = l_True;
                    assert(true_value);
                    break;
                case clingo_truth_value_false:
                    assigns[*start_literal] = l_False;
                    assert(false_value);
                    break;
                default:
                    break;
            }
        }
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
        sum_initUnit = 0;
        sum_Enpropagate = 0;
        sum_Enunit = 0;
        sum_Elimination_Col = 0;
    }
    void printStatistics() {
        cout << "sum_Enconflict:\t" <<  sum_Enconflict << endl;
        cout << "sum_EnGauss:\t" << sum_EnGauss << endl;
        cout << "sum_initEnGauss:\t" << sum_initEnGauss << endl;
        cout << "sum_initUnit:\t" << sum_initUnit << endl;
        cout << "sum_Enpropagate:\t" << sum_Enpropagate << endl;
        cout << "sum_Enunit:\t" << sum_Enunit << endl;
        cout << "sum_Elimination_Col:\t" << sum_Elimination_Col << endl;
    }
    void add_watch_literal(uint32_t lit) {
        if (gwatches[lit].size() > 1) {
            // assert(clingo_propagate_control_has_watch(cpc, lit));
            return;
        };
        // cout << lit << endl;
        assert(gwatches[lit].size() == 1);
        if (cpc) {
            clingo_propagate_control_add_watch(cpc, (clingo_literal_t) lit);
        }
        else {
            assert(cpi);
            clingo_propagate_init_add_watch(cpi, (clingo_literal_t) lit);
        }
    }
    void remove_watch_literal(uint32_t lit) {
        if (!cpc)
            return; 
        // cout << lit << endl;
        // assert(clingo_propagate_control_has_watch(cpc, (clingo_literal_t) lit));
        if (gwatches[lit].size() >= 1) return;
        clingo_propagate_control_remove_watch(cpc, (clingo_literal_t) lit);
    }
    bool is_assignment_conflicting(clingo_propagate_control_t *control) {
        const clingo_assignment_t *values = clingo_propagate_control_assignment(control);
        return clingo_assignment_has_conflict(values);
    }
    bool is_conflicting(vector<Lit> clause, int is_conflict_clause) {
        auto itr = clause.begin() + is_conflict_clause;
        clingo_literal_t insert_lit, test_lit;
        bool result;
        const clingo_assignment_t *values = clingo_propagate_control_assignment(cpc);
        for (auto itr_end = clause.end(); itr != itr_end; itr++) { 
            test_lit = (*itr).var();
            clingo_assignment_is_true(values, test_lit, &result);
            if ((*itr).sign()) {
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
    bool add_clause(vector<Lit> clause, bool is_conflict_clause = false) {
        auto last_literal = literal.end();
        assert(cpc);
        size_t length = clause.size();
        bool result;
        clingo_truth_value_t value;
        clingo_literal_t* new_clause = (clingo_literal_t *)malloc (length * sizeof(clingo_literal_t));
        auto itr = clause.begin();
        u_int32_t index = 0;
        clingo_literal_t insert_lit, test_lit;
        #ifdef DEBUG_MODE
        if (is_conflict_clause) {
            cout << "Conflict clause added : [ "; 
        }
        #endif
        const clingo_assignment_t *values1 = clingo_propagate_control_assignment(cpc);
        for (auto itr_end = clause.end(); itr != itr_end; itr++) {
            test_lit = (*itr).var();
            assert(literal.find(test_lit) != last_literal);
            assert(literal.find(test_lit) != literal.end());
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
            
            insert_lit = (clingo_literal_t)((*itr).sign()) ? (-(*itr).var()) : ((*itr).var());
            #ifdef DEBUG_MODE
            if (is_conflict_clause) {
                cout << insert_lit << " "; 
            }
            #endif
            new_clause[index++] = insert_lit;
        }
        #ifdef DEBUG_MODE
        if (is_conflict_clause) {
            cout << " ]" << endl; 
        }
        #endif
        assert(index == length);
        bool is_conflict = is_assignment_conflicting(cpc); 
        // assert(is_conflicting(clause, !is_conflict_clause));
        if (is_conflict_clause && !clingo_propagate_control_add_clause(cpc, new_clause, length, clingo_clause_type_learnt, &result))
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
        const clingo_assignment_t *values2 = clingo_propagate_control_assignment(cpc);
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
        if (!is_conflict_clause && !clingo_propagate_control_add_clause(cpc, new_clause, length, clingo_clause_type_learnt, &result))
        {
            (is_conflict_clause) ? printf("\nConflict\n") : printf("\nPropagation\n");
            
            cout << "\nCan't insert clause\n";
            
        }
        if (!result) {
            return false;
        }
        if (!clingo_propagate_control_propagate(cpc, &result))
        {
            cout << "Can't propagate clause";
        }
        if (!result) {
            return false;
        }
        get_assignment(cpc);
        free(new_clause);
        assert(result);  // this is propagating
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
};

// }


#endif //SOLVERSTATE_H_
