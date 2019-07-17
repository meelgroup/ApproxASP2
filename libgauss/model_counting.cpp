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


#include "utility.h"

using std::cout;
using std::endl;

//TODO fix!!!
#define TIMEOUT 10

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
    printf("#Clasp_calls: %d & #Calls_timeouted: %d", con->clasp_call, con->clasp_call_timeout);
}
void do_initial_setup(clingo_control_t** ctl, Configuration* con)
{
    clingo_part_t parts[] = {{"base", NULL, 0}};
    if (*ctl) {
        printf("Here...");
        clingo_control_free(*ctl);
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
}

unsigned Bounded_counter(clingo_control_t* ctl, Configuration* con, bool gen_xor, bool prefix_slice,
                         bool no_xor = false, unsigned m_value = 0)
{
    if (!no_xor && gen_xor) {
        // we will generate k xors...
        generate_k_xors(m_value, con);
    } else if (!no_xor && !gen_xor) {
        // we will take prefix slice of previously generated xor
        int generated_xor = con->xor_cons.size();
        if (generated_xor < m_value) {
            // need (m_value - generated_xor) more xors
            generate_k_xors(m_value, con);
        }
    }
    if (!ctl)
        do_initial_setup(&ctl, con);
    if (con->xor_last_added - 1 > m_value) {
        do_initial_setup(&ctl, con);
    }
    if (con->xor_last_added - 1 < m_value) {
        // translation(ctl, con, con->xor_last_added, m_value);
    }
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
        unsigned result = Bounded_counter(control, con, generate_xor, true, false, m_value);
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
            big_cell[m_value] = true;
            count_list[m_value] = result;
            hi_index = m_value;
            if (abs(m_value - m_prev) < 3 && m_prev != 0) {
                hi_index = m_value;
                m_value--;
            } else {
                if (hash_prev > m_value)
                    hash_prev = 0;
                hi_index = m_value;
                lo_index = hash_prev;
                m_value = (lo_index + hi_index) >> 1;
            }
        }
        hash_prev = swap_var;
    }
    return ret;
}

SATCount ApproxSMCCore(clingo_control_t* control, Configuration* con)
{
    int counter = 0, prev_cells = 1, minHash = 0,
        medSolCount = 0; // in previous version prev_cells = 2 ^ 1 = 2
    unsigned count, n_cell;
    SATCount solCount;
    std::list<int> numHashList, numCountList, medianComputeList;
    while (counter < con->t) {
        counter++;
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
            cout << "Iteration: " << counter << " completed!!!" << endl;
            solCount.cellSolCount = medSolCount;
            solCount.hashCount = minHash;
        }
    }
    return solCount;
}

void ApproxSMC(clingo_control_t* control, Configuration* con)
{
    // clingo_part_t parts[] = {{"base", NULL, 0}};
    // clingo_control_new(con->asp_argument, con->argu_count, NULL, NULL, 20, &control);
    SATCount solCount;
    do_initial_setup(&control, con);
    get_symbol_atoms(control, con);
    con->number_of_active_atoms = con->active_atoms.size();

    int count = Bounded_counter(control, con, false, false, true, 0);
    printf("%d", count);
}