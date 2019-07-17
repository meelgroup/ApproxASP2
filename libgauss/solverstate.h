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
    uint32_t sum_initTwo;
    uint32_t sum_Enconflict;
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
        clingo_assignment_t *values = clingo_propagate_control_assignment(control);
        decision_level = clingo_assignment_decision_level(values);
        clingo_truth_value_t value;
        assigns.assign(nVars(), l_Undef);
        auto start_literal = literal.begin(); 
        for (auto end_literal = literal.end(); start_literal != end_literal ; start_literal++)
        {
            assert(clingo_assignment_has_literal(values, *start_literal));
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
        sum_initTwo = 0;
        sum_Enpropagate = 0;
        sum_Enunit = 0;
    }
    void printStatistics() {
        cout << "sum_Enconflict:\t" <<  sum_Enconflict << endl;
        cout << "sum_EnGauss:\t" << sum_EnGauss << endl;
        cout << "sum_initEnGauss:\t" << sum_initEnGauss << endl;
        cout << "sum_initUnit:\t" << sum_initUnit << endl;
        cout << "sum_initTwo:\t" << sum_initTwo << endl;
        cout << "sum_Enpropagate:\t" << sum_Enpropagate << endl;
        cout << "sum_Enunit:\t" << sum_Enunit << endl;
    }
    void add_watch_literal(uint32_t lit) {
        if (gwatches[lit].size() > 1) return;
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
        if (gwatches[lit].size() >= 1) return;
        clingo_propagate_control_remove_watch(cpc, (clingo_literal_t) lit);
    }

    void add_clause(vector<Lit> clause, bool xor_add = false) {
        auto last_literal = literal.end();
        assert(cpc);
        size_t length = clause.size();
        bool result;
        clingo_literal_t* new_clause = new clingo_literal_t[length];
        auto itr = clause.begin();
        u_int32_t index = 0;
        clingo_literal_t insert_lit, test_lit;
        for (auto itr_end = clause.end(); itr != itr_end; itr++) {
            test_lit = (*itr).var();
            assert (literal.find(test_lit) != last_literal); 
            insert_lit = (clingo_literal_t)((*itr).sign()) ? (-(*itr).var()) : ((*itr).var());
            new_clause[index++] = insert_lit;
        }
        assert(index == length);
        if (!clingo_propagate_control_add_clause(cpc, new_clause, length, clingo_clause_type_volatile, &result))
        {
            cout << "Can't insert clause";
        }
        // if it is a binary clause then add one more new clause
        if (xor_add)
        {
            assert(length == 2);
            new_clause[0] = -new_clause[0];
            new_clause[1] = -new_clause[1];
            if (!clingo_propagate_control_add_clause(cpc, new_clause, length, clingo_clause_type_volatile, &result))
            {
                cout << "Can't insert clause";
            }
        }
    }
};

// }


#endif //SOLVERSTATE_H_
