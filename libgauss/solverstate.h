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
        auto start = high_resolution_clock::now();
        cpc = control;
        const clingo_assignment_t *values = clingo_propagate_control_assignment(control);
        // decision_level = clingo_assignment_decision_level(values);
        clingo_truth_value_t value;
        assigns.assign(nVars(), l_Undef);
        auto start_literal = literal.begin(); 
        for (auto end_literal = literal.end(); start_literal != end_literal ; start_literal++)
        {
            #ifdef DEBUG
            assert(clingo_assignment_has_literal(values, *start_literal));
            #endif
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
        auto stop = high_resolution_clock::now();
        problem.clingo_assignment_time += duration_cast<microseconds>(stop - start).count() / pow(10, 6);
        problem.clingo_assignment_called++;
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
        }
        else {
            assert(cpi);
            clingo_propagate_init_add_watch(cpi, (clingo_literal_t) lit);
        }
    }
    void remove_watch_literal(uint32_t lit) {
        if (!cpc)
            return; 
        if (gwatches[lit].size() >= 1) return;
        clingo_propagate_control_remove_watch(cpc, (clingo_literal_t) lit);
    }
    bool is_assignment_conflicting(clingo_propagate_control_t *control) {
        const clingo_assignment_t *values = clingo_propagate_control_assignment(control);
        return clingo_assignment_has_conflict(values);
    }
    bool add_clause(vector<Lit> clause, bool is_conflict_clause = false) {
        auto start = high_resolution_clock::now();
        auto last_literal = literal.end();
        assert(cpc);
        size_t length = clause.size();
        bool result;
        clingo_literal_t* new_clause = (clingo_literal_t *)malloc (length * sizeof(clingo_literal_t));
        auto itr = clause.begin();
        u_int32_t index = 0;
        clingo_literal_t insert_lit, test_lit;
        for (auto itr_end = clause.end(); itr != itr_end; itr++) {
            test_lit = (*itr).var();
            #ifdef DEBUG
            assert(literal.find(test_lit) != last_literal);
            assert(literal.find(test_lit) != literal.end());
            if (index == 0 && !is_conflict_clause) {
                assert(assigns[test_lit] == l_Undef);
            }
            else if ((*itr).sign())
            {
                assert(assigns[test_lit] == l_True);
            }
            else
            {
                assert(assigns[test_lit] == l_False);
            }
            #endif
            insert_lit = (clingo_literal_t)((*itr).sign()) ? (-(*itr).var()) : ((*itr).var());
            new_clause[index++] = insert_lit;
        }
        // assert(index == length);
        // bool is_conflict = is_assignment_conflicting(cpc); 	
        // assert(is_conflicting(clause, !is_conflict_clause));	
        if (is_conflict_clause && !clingo_propagate_control_add_clause(cpc, new_clause, length, clingo_clause_type_volatile, &result))	
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
        if (!is_conflict_clause && !clingo_propagate_control_add_clause(cpc, new_clause, length, clingo_clause_type_volatile, &result))	
        {	
            (is_conflict_clause) ? printf("\nConflict\n") : printf("\nPropagation\n");	
            	
            cout << "\nCan't insert clause\n";	
            	
        }	
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
        free(new_clause);
        auto stop = high_resolution_clock::now();
        problem.clingo_add_clause_time += duration_cast<microseconds>(stop - start).count() / pow(10, 6);
        assert(result);
    }
    bool add_initial_clause(vector<Lit> clause) {
        assert(cpi);
        assert(clause.size() == 1);
        clingo_literal_t* new_clause = (clingo_literal_t *)malloc (sizeof(clingo_literal_t));
        if (clause[0].sign()) {
            new_clause[0] = -clause[0].var();
        }
        else {
            new_clause[0] = clause[0].var();
        }
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
