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


#include <assert.h>
#include <clingo.h>
#include <stdio.h>
#include <time.h>
#include <list>
#include <cmath>
#include <iostream>
#include <chrono>


#include "utility.h"
#include "propagator.h"
#include "solverstate.h"

using std::cout;
using std::endl;
using namespace std::chrono;
std::list<int> numHashList, numCountList, medianComputeList;
//TODO fix!!!
#define TIMEOUT 1000

int findMin(std::list<int> numList)
{
    assert(numList.size() >= 1);
    int min;
    for (std::list<int>::iterator it = numList.begin(); it != numList.end(); it++) {
        if (it == numList.begin()) {
            min = *it;
        } else if ((*it) < min) {
            min = *it;
        }
    }
    return min;
}

double findMedian(std::list<int> numList)
{
    numList.sort();
    int medIndex = int((numList.size()) / 2);
    std::list<int>::iterator it = numList.begin();
    if (medIndex >= (int)numList.size()) {
        std::advance(it, numList.size() - 1);
        return double(*it);
    }
    std::advance(it, medIndex);
    return double(*it);
}
void print_count(SATCount ret)
{
    printf("Approximate count: %d X 2 ^ %d.\n", ret.cellSolCount, ret.hashCount);
}
void print_stat(Configuration* con)
{
    printf("\nClasp is called: %d times & Clasp is timeouted: %d times.\n", con->clasp_call, con->clasp_call_timeout);
}
void do_initial_setup(clingo_control_t** ctl, Configuration* con, int m_value)
{
    clingo_part_t parts[] = {{"base", NULL, 0}};
    if (*ctl) {
        // printf("Here...");
        // clingo_control_free(*ctl);
        *ctl = NULL;
    }
    clingo_control_new(con->asp_argument, con->argu_count, NULL, NULL, 20, ctl);
    // clingo_control_add(*ctl, "base", NULL, 0, "{a; b; c; d; e; f}.");
    clingo_control_load(*ctl, con->asp_file.c_str());
    if (con->input_file) {
        // printf("Input file: %s", con->input_file);
        clingo_control_load(*ctl, con->input_file);
    }

    con->xor_last_added = 1;
    clingo_control_ground(*ctl, parts, 1, NULL, NULL);
    
    std::string parity_string;
    parity_string.clear();
    if (m_value > 0) {
        parity_string = get_parity_string(con, m_value);
        clingo_control_add(*ctl, "base", NULL, 0, parity_string.c_str());
        clingo_part_t parts[] = {{"base", NULL, 0}};
        // clingo_control_ground(*ctl, parts, 1, NULL, NULL);
    }
    clingo_control_ground(*ctl, parts, 1, NULL, NULL);
}

unsigned Bounded_counter(clingo_control_t* ctl, Configuration* con,
     unsigned m_value)
{
    // if (!no_xor && gen_xor) {
    //     // we will generate k xors...
    //     generate_k_xors(m_value, con);
    // } else if (!no_xor && !gen_xor) {
    //     // we will take prefix slice of previously generated xor
    //     int generated_xor = con->xor_cons.size();
    //     if (generated_xor < m_value) {
    //         // need (m_value - generated_xor) more xors
    //         generate_k_xors(m_value, con);
    //     }
    // }
    do_initial_setup(&ctl, con, m_value);
    clingo_propagator_t prop = {
        (bool (*)(clingo_propagate_init_t *, void *))init,
        (bool (*)(clingo_propagate_control_t *, clingo_literal_t const *, size_t, void *))propagate,
        NULL,
        (bool (*)(clingo_propagate_control_t *, void *))check};
    // user data for the propagator
    propagator_t prop_data = {};
    prop_data.max_assumption_var = m_value;
    // if (!ctl)
    //     do_initial_setup(&ctl, con);
    // if (con->xor_last_added - 1 > m_value) {
    //     do_initial_setup(&ctl, con);
    // }
    // if (con->xor_last_added - 1 < m_value) {
    //     // translation(ctl, con, con->xor_last_added, m_value);
    // }
    clingo_control_register_propagator(ctl, &prop, &prop_data, true);
    clingo_solve_handle_t* handle;
    clingo_model_t const* model;
    clingo_control_solve(ctl, clingo_solve_mode_async | clingo_solve_mode_yield, NULL, 0, NULL,
                         NULL, &handle);
    bool finished = false;
    double remaining_time = TIMEOUT;
    clock_t tStart = clock();
    unsigned model_count = 0;
    while (true) {
        clingo_solve_handle_resume(handle);
        remaining_time = TIMEOUT - (double)(clock() - tStart) / CLOCKS_PER_SEC;
        finished = false;
        if (remaining_time > 0)
            clingo_solve_handle_wait(handle, remaining_time, &finished);
        if (!finished)
            break;
        clingo_solve_handle_model(handle, &model);
        if (!model)
            break;
        model_count++;
    }
    clingo_solve_handle_cancel(handle);
    add_execution_time(ctl, con);
    con->clasp_call++;
    if (!finished)
        con->clasp_call_timeout++;
    if (con->clasp_call > 0 && con->clasp_call % con->interval == 0)
        print_stat(con);
    return finished ? model_count : -1;
}

SATCount LogSATSearch(clingo_control_t* control, Configuration* con, int m_prev)
{
    std::unordered_map<int, bool> big_cell;
    std::unordered_map<int, int> count_list;
    int lo_index = 0, hi_index = con->number_of_active_atoms, swap_var;
    int m_value = m_prev, num_explored = 1, hash_prev = 0, repeat_try = 0;
    bool generate_xor = true;
    assert(m_prev <= con->number_of_active_atoms);
    SATCount ret;
    ret.cellSolCount = -1;
    while (num_explored < con->number_of_active_atoms) {
        swap_var = m_value;
        auto start = high_resolution_clock::now();
        unsigned result = Bounded_counter(control, con, m_value);
        auto stop = high_resolution_clock::now();
        cout << "c execution time: " << duration_cast<microseconds>(stop - start).count() / pow(10, 6) << " seconds." << endl;
        
        generate_xor = false;
        if (result == -1) {
            if (repeat_try < 2) {
                generate_xor = true;
                repeat_try++;
            } else {
                m_value++;
                repeat_try = 0;
            }
        } else if (result > con->thresh) {
            num_explored = m_value - hi_index + con->number_of_active_atoms;
            auto finder = big_cell.find(m_value + 1);
            if (finder != big_cell.end() && finder->second == false) {
                assert(count_list.find(m_value + 1) != count_list.end());
                ret.cellSolCount = count_list.find(m_value + 1)->second;
                ret.hashCount = m_value + 1;
                return ret;
            }
            big_cell[m_value] = true;
            if (abs(m_value - m_prev) < 2 && m_prev != 0) {
                lo_index = m_value;
                m_value++;
            } else if ((lo_index + (m_value - lo_index) * 2) >= hi_index - 1) {
                lo_index = m_value;
                m_value = (lo_index + hi_index) >> 1;
            } else
                m_value = lo_index + (m_value - lo_index) * 2;
        }

        else if (result <= con->thresh) {
            num_explored = lo_index - m_value + con->number_of_active_atoms;
            auto finder = big_cell.find(m_value - 1);
            if (finder != big_cell.end() && finder->second == true) {
                ret.cellSolCount = result;
                ret.hashCount = m_value;
                return ret;
            }
            big_cell[m_value] = false;
            count_list[m_value] = result;
            hi_index = m_value;
            if (abs(m_value - m_prev) < 3 && m_prev != 0) {
                hi_index = m_value;
                m_value--;
            } else {
                if (hash_prev > m_value)
                    hash_prev = 0;
                hi_index = m_value;
                if (hash_prev > lo_index) {
                    lo_index = hash_prev;
                }
                m_value = (lo_index + hi_index) >> 1;
            }
        }
        hash_prev = swap_var;
    }
    return ret;
}

SATCount ApproxSMCCore(clingo_control_t* control, Configuration* con, int counter)
{
    int prev_cells = 1, minHash = 0,
        medSolCount = 0; // in previous version prev_cells = 2 ^ 1 = 2
    unsigned count, n_cell;
    SATCount solCount;
    if (numHashList.size() > 0) {
        prev_cells = numHashList.back();
    }
    cout << "ApproxSMCCore iteration: " << counter << " started ..." << endl;
    solCount = LogSATSearch(control, con, prev_cells);
    if (solCount.cellSolCount != -1) {
        prev_cells = n_cell;
        numCountList.push_back(solCount.cellSolCount);
        numHashList.push_back(solCount.hashCount);
        minHash = findMin(numHashList);
        medianComputeList.clear();
        assert(numHashList.size() == numCountList.size());
        for (std::list<int>::iterator it1 = numHashList.begin(), it2 = numCountList.begin();
                it1 != numHashList.end() && it2 != numCountList.end(); it1++, it2++) {
            medianComputeList.push_back((*it2) * std::pow(2, (*it1) - minHash));
        }
        assert(numHashList.size() == medianComputeList.size());
        medSolCount = findMedian(medianComputeList);
        cout << "ApproxSMCCore iteration: " << counter << " completed !!!" << endl;
        solCount.cellSolCount = medSolCount;
        solCount.hashCount = minHash;
        cout << "After the iteration, the (median) number of solution: " << solCount.cellSolCount << " * 2 ^ " << solCount.hashCount << endl; 
    }
    
    return solCount;
}

void ApproxSMC(clingo_control_t* control, Configuration* con)
{
    // clingo_part_t parts[] = {{"base", NULL, 0}};
    // clingo_control_new(con->asp_argument, con->argu_count, NULL, NULL, 20, &control);
    SATCount solCount;
    do_initial_setup(&control, con, 0);
    get_symbol_atoms(control, con);
    con->number_of_active_atoms = con->active_atoms.size();
    if (problem.use_ind_sup)
        con->number_of_active_atoms = con->active_atoms_ind_sup.size();
    // first of all checking whether the problem is trivial or not
    unsigned result = Bounded_counter(control, con, 0);
    if (result <= con->thresh) {
        cout << "We calculated the exact number of solutions." << endl;
        cout << "The exact number of solution: " << result << " * 2 ^ " << 0 << endl;
        return;
    }
    cout << "The problem has more than thresh number of solutions" << endl;
    
    // the problem is not trivial, so we are running approxmc
    int counter = 0;
    while (counter < con->t) {
        counter++;
        generate_k_xors(con->number_of_active_atoms - 1, con);
        translation(&control, con, false, std::cout, 1, -1);
        solCount = ApproxSMCCore(control, con, counter);
        con->xor_cons.clear();
        con->seed = counter + 1;
    }
}
