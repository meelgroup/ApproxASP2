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

#include <clingo.h>
#include <unordered_map>
#include "EGaussian.h"
#include "gqueuedata.h"
#include "solverstate.h"
#include "xor.h"
#include "utility.h"
#include "propagator.h"

using std::vector;
typedef struct {
    // assignment of pigeons to holes
    // (hole number -> pigeon placement literal or zero)
    clingo_literal_t *holes;
    size_t size;
} state_t;

bool init_all_matrixes(propagator_t *prop)
{
    assert(prop->solver->ok);

    vector<EGaussian *>::iterator i = prop->gmatrixes.begin();
    vector<EGaussian *>::iterator j = i;
    vector<EGaussian *>::iterator gend = prop->gmatrixes.end();
    for (; i != gend; i++) {
        EGaussian *g = *i;
        bool created = false;
        // initial arrary. return true is fine , return false means solver already false;
        // assert(false && "THE BUG IS HERE MAHI! You must add all the propagations to the solver fom the full_init!!!");
        if (!g->full_init(created)) {
            return false;
        }
        if (!prop->solver->ok) {
            break;
        }
        if (created) {
            *j++ = *i;
        } else {
            delete g;
        }
    }
    while (i != gend) {
        *j++ = *i++;
    }
    prop->gmatrixes.resize(prop->gmatrixes.size() - (i - j));
    prop->gqueuedata.resize(prop->gmatrixes.size());
    for (auto &gqd: prop->gqueuedata) {
        gqd.reset_stats();
    }

    return prop->solver->okay();
}

bool get_arg(clingo_symbol_t sym, int offset, int *num)
{
    clingo_symbol_t const *args;
    size_t args_size;
    // get the arguments of the function symbol
    if (!clingo_symbol_arguments(sym, &args, &args_size)) {
        return false;
    }
    // get the requested numeric argument
    if (!clingo_symbol_number(args[offset], num)) {
        return false;
    }

    return true;
}

clingo_symbol_t get_arg_str(clingo_symbol_t sym, int offset, char **str_argu)
{
    clingo_symbol_t const *args;
    size_t args_size;
    // get the arguments of the function symbol
    if (!clingo_symbol_arguments(sym, &args, &args_size)) {
        return false;
    }
    // get the requested numeric argument
    string_buffer_t buf = {NULL, 0};
    get_symbol_string(args[offset], &buf);
    *str_argu = (char *)malloc((buf.string_n) * sizeof(char));
    strcpy(*str_argu, buf.string);
    return args[offset];
}

void clearEnGaussMatrixes(propagator_t *prop)
{
    for (auto &gqd: prop->gqueuedata) {
        gqd.reset_stats();
    }
    //cout << "Clearing matrixes" << endl;
    for (EGaussian *g: prop->gmatrixes) {
        delete g;
    }
    if (prop->solver) {
        for (auto &w: prop->solver->gwatches) {
            w.clear();
        }
    }
    prop->gmatrixes.clear();
    prop->gqueuedata.clear();
}

bool init(clingo_propagate_init_t *init, propagator_t *data)
{
    // the total number of holes pigeons can be assigned too
    int holes = 0;

    size_t threads = clingo_propagate_init_number_of_threads(init);
    // stores the (numeric) maximum of the solver literals capturing pigeon placements
    // note that the code below assumes that this literal is not negative
    // which holds for the pigeon problem but not in general
    clingo_literal_t max = 0;
    const clingo_symbolic_atoms_t *atoms;
    clingo_signature_t sig;
    clingo_symbolic_atom_iterator_t atoms_it, atoms_ie, finder;
    string_buffer_t buf = {NULL, 0};
    vector<Xor> xorclauses;
    vector<bool> xorparity;
    std::unordered_map<clingo_symbol_t, clingo_literal_t> symbol_to_literal;
    std::unordered_map<int, vector<clingo_symbol_t>> xor_to_symbol;
    std::unordered_set<clingo_literal_t> solver_literal;

    // ensure that solve can be called multiple times
    // for simplicity, the case that additional holes or pigeons to assign are grounded is not handled here

    // the propagator monitors place/2 atoms and dectects conflicting assignments
    // first get the symbolic atoms handle
    if (!clingo_propagate_init_symbolic_atoms(init, &atoms)) {
        return false;
    }
    // create place/2 signature to filter symbolic atoms with
    if (!clingo_signature_create("__parity", 2, true, &sig)) {
        return false;
    }
    // get an iterator after the last place/2 atom
    // (atom order corresponds to grounding order (and is unpredictable))
    if (!clingo_symbolic_atoms_end(atoms, &atoms_ie)) {
        return false;
    }

    // loop over the place/2 atoms in two passes
    // the first pass determines the maximum placement literal
    // the second pass allocates memory for data structures based on the first pass
    if (!clingo_symbolic_atoms_begin(atoms, &sig, &atoms_it)) {
        return false;
    }
    char *parity;
    int xor_count = (data->max_assumption_var > 0) ? data->max_assumption_var : 0;
    clingo_literal_t largest_var = std::numeric_limits<uint32_t>::max();
    // if (xor_count == 0){
    //     while (true) {
    //         int id;
    //         char *s;
    //         bool equal;
    //         clingo_literal_t lit, lit2;
    //         clingo_symbol_t sym;
    //         // stop iteration if the end is reached
    //         if (!clingo_symbolic_atoms_iterator_is_equal_to(atoms, atoms_it, atoms_ie, &equal)) {
    //             return false;
    //         }
    //         if (equal) {
    //             break;
    //         }
    //         // get the solver literal for the placement atom
    //         if (!clingo_symbolic_atoms_literal(atoms, atoms_it, &lit2)) {
    //             return false;
    //         }
    //         // printf("clingo_symbolic_atoms_literal: %d.\n", lit);
    //         if (!clingo_propagate_init_solver_literal(init, lit2, &lit)) {
    //             return false;
    //         }
    //         // printf("clingo_propagate_init_solver_literal: %d.\n", lit);

    //         // extract the hole number from the atom
    //         if (!clingo_symbolic_atoms_symbol(atoms, atoms_it, &sym)) {
    //             return false;
    //         }
    //         get_arg(sym, 0, &id);
    //         get_arg_str(sym, 1, &parity);
    //         assert(!strcmp(parity, "odd") || !strcmp(parity, "even"));
    //         if (id + 1 > xor_count)
    //             xor_count = id + 1;
    //         //   get_symbol_string(sym, &buf);
    //         //   printf("get_arg_str: %s.\n", s);
    //         //   printf("get_symbol_string: %lu -> %s.\n", lit, buf.string);

    //         // advance to the next placement atom
    //         if (!clingo_symbolic_atoms_next(atoms, atoms_it, &atoms_it)) {
    //             return false;
    //         }
    //     }
    // }
    printf("Total XOR constraints: %d.\n", xor_count);
    xorparity.resize(xor_count);
    if (!clingo_signature_create("__parity", 3, true, &sig)) {
        return false;
    }
    // get an iterator after the last place/2 atom
    // (atom order corresponds to grounding order (and is unpredictable))
    if (!clingo_symbolic_atoms_end(atoms, &atoms_ie)) {
        return false;
    }

    // loop over the place/2 atoms in two passes
    // the first pass determines the maximum placement literal
    // the second pass allocates memory for data structures based on the first pass
    if (!clingo_symbolic_atoms_begin(atoms, &sig, &atoms_it)) {
        return false;
    }
    char *condition;
    clingo_literal_t lit, lit2;
    clingo_symbol_t sym;
    while (true) {
        int id;
        char *s;
        bool equal;
        // stop iteration if the end is reached
        if (!clingo_symbolic_atoms_iterator_is_equal_to(atoms, atoms_it, atoms_ie, &equal)) {
            return false;
        }
        if (equal) {
            break;
        }
        // get the solver literal for the placement atom
        if (!clingo_symbolic_atoms_literal(atoms, atoms_it, &lit2)) {
            return false;
        }
        // printf("clingo_symbolic_atoms_literal: %d.\n", lit);
        if (!clingo_propagate_init_solver_literal(init, lit2, &lit)) {
            return false;
        }
        // printf("clingo_propagate_init_solver_literal: %d.\n", lit);

        // extract the hole number from the atom
        if (!clingo_symbolic_atoms_symbol(atoms, atoms_it, &sym)) {
            return false;
        }
        get_arg(sym, 0, &id);
        if (id >= xor_count) {
            clingo_symbolic_atoms_next(atoms, atoms_it, &atoms_it);
            continue;
        }
        get_arg_str(sym, 1, &parity);
        sym = get_arg_str(sym, 2, &condition);
        assert(id < xor_count);
        assert(!strcmp(parity, "odd") || !strcmp(parity, "even"));
        xorparity[id] = (!strcmp(parity, "odd")) ? 1 : 0;
        symbol_to_literal[sym] = 0;
        xor_to_symbol[id].push_back(sym);

        // advance to the next placement atom
        if (!clingo_symbolic_atoms_next(atoms, atoms_it, &atoms_it)) {
            return false;
        }
    }
    if (!clingo_symbolic_atoms_end(atoms, &atoms_ie)) {
        return false;
    }
    bool equal;
    for (auto it = symbol_to_literal.begin(); it != symbol_to_literal.end(); ++it) {
        equal = false;
        clingo_symbolic_atoms_find(atoms, it->first, &finder);
        clingo_symbolic_atoms_iterator_is_equal_to(atoms, finder, atoms_ie, &equal);
        assert(!equal);
        clingo_symbolic_atoms_literal(atoms, finder, &lit2);
        clingo_propagate_init_solver_literal(init, lit2, &lit);
        largest_var = (lit > largest_var) ? lit : largest_var;
        it->second = lit;
        solver_literal.insert(lit);
    }
    auto each_xor = xor_to_symbol.begin();
    for (auto xor_end = xor_to_symbol.end(); each_xor != xor_end; each_xor++) {
        assert(each_xor->second.size() > 0);
        auto symbol = each_xor->second.begin();
        vector<uint32_t> temp_xorclause;
        temp_xorclause.clear();
        for (auto symbol_end = each_xor->second.end(); symbol != symbol_end; symbol++) {
            auto symbol_finder = symbol_to_literal.find(*symbol);
            assert(symbol_finder != symbol_to_literal.end());
            assert(symbol_finder->second > 0);
            temp_xorclause.push_back(symbol_finder->second);
        }
        xorclauses.push_back(Xor(temp_xorclause, xorparity[each_xor->first]));
    }
    printf("largest_var %d.\n", largest_var);
    assert(xorclauses.size() == xor_count);
    if (xor_count > 0) {
        data->gqueuedata.clear();
        clearEnGaussMatrixes(data);
        data->gqueuedata.resize(1);
        data->solver = new SolverState(largest_var, init, solver_literal);
        data->gmatrixes.push_back(new EGaussian(data->solver, 0, xorclauses));
        // printf("propagation %d.\n", data->solver->value(largest_var));
        
        if (!init_all_matrixes(data)) {
            return false;
        }
        // data->solver->printStatistics();
        // cout << "here" << endl;
    }
    return true;
}
bool gauss_elimation(clingo_propagate_control_t *control, const clingo_literal_t *changes,
                     size_t size, propagator_t *data)
{
    bool immediate_break = false;
    for (auto &gqd: data->gqueuedata) {
        gqd.reset();
    }
    for (size_t gqhead = 0; gqhead < size; ++gqhead) {
        // the freshly assigned literal
        const Lit p = Lit((int)changes[gqhead], (changes[gqhead] < 0));
        assert(changes[gqhead] > 0 && "My understanding is wrong");
        vec<GaussWatched> &ws = data->solver->gwatches[p.var()];
        GaussWatched *i = ws.begin();
        GaussWatched *j = i;
        const GaussWatched *end = ws.end();
        // assert(i != end);
        if (i == end)
            continue;

        for (; i != end; i++) {
            data->gqueuedata[i->matrix_num].enter_matrix = true;
            if (!data->gmatrixes[i->matrix_num]->find_truths2(
                i, j, p.var(), i->row_id,
                data->gqueuedata[i->matrix_num])
            ) {
                //conflict
                immediate_break = true;
                break;
            } else if (!data->gqueuedata[i->matrix_num].prop_clause_gauss.empty()){
                //must propagate
                data->solver->sum_Enpropagate++;
                data->solver->add_clause(
                    data->gqueuedata[i->matrix_num].prop_clause_gauss, false);
                return true;
            }
        }

        if (i != end) {
            i++;
            //copy remaining watches
            GaussWatched *j2 = j;
            GaussWatched *i2 = i;
            for (; i2 != end; i2++) {
                *j2 = *i2;
                j2++;
            }
        }
        ws.shrink_(i - j);
        data->solver->remove_watch_literal(p.var());
        for (size_t g = 0; g < data->gqueuedata.size(); g++)
            if (data->gqueuedata[g].do_eliminate)
                data->gmatrixes[g]->eliminate_col2(p.var(), data->gqueuedata[g], immediate_break);

        if (immediate_break)
            break;
    }
    for (GaussQData &gqd: data->gqueuedata) {
        if (gqd.enter_matrix) {
            data->gqueuedata[0].big_gaussnum++;
            data->solver->sum_EnGauss++;
        }
        switch (gqd.ret_gauss) {
            case 1:
                assert(false);
                exit(-1);
                break;

            case 0: {
                lbool ret;
                gqd.big_conflict++;
                data->solver->sum_Enconflict++;
                data->solver->add_clause(gqd.conflict_clause_gauss, true);
                return true;
            }

            case 2: // propagation
            case 3: // unit propagation
                gqd.big_propagate++;
                data->solver->sum_Enpropagate++;
                data->solver->add_clause(gqd.prop_clause_gauss, false);
            case 4:
                //nothing
                break;

            default:
                assert(false);
                // return l_Nothing;
        }
    }
    // data->solver->printStatistics();
    return true;
}
bool propagate(clingo_propagate_control_t *control, const clingo_literal_t *changes, size_t size,
               propagator_t *data)
{
    // get the thread specific state
    if (data->max_assumption_var == 0) {
        return true;
    } 
    data->solver->get_assignment(control);
    gauss_elimation(control, changes, size, data);
    return true;
}

bool undo(clingo_propagate_control_t *control, const clingo_literal_t *changes, size_t size,
          propagator_t *data)
{
    // get the thread specific state
    for (EGaussian *gauss: data->gmatrixes) {
        gauss->canceling();
    }
    // data->solver->get_assignment(control);
    return true;
}

bool check(clingo_propagate_control_t *control, propagator_t *data)
{
    // static int c = 0;
    // c++;
    // get the thread specific state
    if (data->max_assumption_var == 0) {
        return true;
    }
    data->solver->get_assignment(control);
    // auto start_literal = data->solver->literal.begin(); 
    // for (auto end_literal = data->solver->literal.end(); start_literal != end_literal ; start_literal++)
    // {
    //     if (data->solver->assigns[*start_literal] == l_True) {
    //         std::cout << *start_literal << " ";
    //     }
    // }
    // std::cout << "\n";
    bool immediate_break = false;
    for (auto &gqd: data->gqueuedata) {
        gqd.reset();
    }
    // std::cout << "It is called: " << c << std::endl;
    for (size_t g = 0; g < data->gqueuedata.size(); g++)
    {
        data->gmatrixes[g]->check_xor(data->gqueuedata[g], immediate_break);

        if (immediate_break)
        {
            for (GaussQData &gqd: data->gqueuedata) {
                data->solver->sum_Enconflict++;
                data->solver->add_clause(gqd.conflict_clause_gauss, true);
            }
            return true;
        }
    }
    // std::cout << "One model found ... " << std::endl;
    return true;
}
