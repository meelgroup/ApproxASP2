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
#include <math.h>
#include <cstring>
#include <ctime>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

#include "utility.h"
#include "iterations.h"

using std::string;
extern Configuration problem;
int compute_pivot(float xi)
{
    assert(xi > 0.0 && xi < 1.0);
    return (int)1 + 9.84 * (1 + (xi / (1 + xi))) * pow((1 + 1 / xi), 2);
}

int compute_iteration(Configuration *con)
{
    assert(con->conf > 0.0 && con->conf < 1.0);
    int iterations = 1;
    for (int count = 0; count < 256; count++) {
        con->confidences.push_back(iterationConfidences[count]);
        if (iterationConfidences[count] >= 1 - con->conf) {
            iterations = count * 2 + 1;
            break;
        }
    }
    return iterations;
}

float in_range(char const *label, float conf)
{
    float number = atof(label);
    if (number > 0.0 && number < 1.0) {
        return number;
    }
    return conf;
}
float confidence(char const *label, float value)
{
    return in_range(label, value);
}
float tolerance(char const *label, float value)
{
    return in_range(label, value);
}

unsigned iteration_count(char const *label, float value)
{
    unsigned number = atoi(label);
    if (number > 0)
        return number;
    else
        return value;
}

void get_symbol_string(clingo_symbol_t symbol, string_buffer_t *buf)
{
    char *string;
    size_t n;

    clingo_symbol_to_string_size(symbol, &n);

    if (buf->string_n < n) {
        string = (char *)realloc(buf->string, sizeof(*buf->string) * n);
        buf->string = string;
        buf->string_n = n;
    }
    // retrieve the symbol's string
    clingo_symbol_to_string(symbol, buf->string, n);
}

void reset_Configuration(Configuration *con)
{
    con->clasp_call = 0;
    con->clasp_call_timeout = 0;
    con->time_in_clasp = 0.0;
}

string atom_to_symbol(clingo_symbol_t atom, Configuration *con)
{
    auto it = con->atom_symbol_map.find(atom);
    assert(it != con->atom_symbol_map.end());
    return it->second;
}

std::vector<clingo_symbol_t> selectKItems(std::vector<clingo_symbol_t> stream)
{
    int i; // index for elements in stream[]
    int n = stream.size();
    int k = n / 2;
    std::vector<clingo_symbol_t> reservoir;
    for (i = 0; i < k; i++)
        reservoir.push_back(stream[i]);

    // Use a different seed value so that we don't get
    // same result each time we run this program

    // Iterate from the (k+1)th element to nth element
    for (; i < n; i++) {
        // std::cout << "rand()" << rand() % (i + 1) << std::endl;
        // Pick a random index from 0 to i.
        int j = rand() % (i + 1);

        // If the randomly  picked index is smaller than k, then replace
        // the element present at the index with new element from stream
        if (j < k)
            reservoir[j] = stream[i];
    }
    assert(reservoir.size() == k);
    return reservoir;
}

void get_symbol_atoms(clingo_control_t *ctl, Configuration *con)
{
    assert(ctl != NULL);
    const clingo_symbolic_atoms_t *atoms;
    clingo_symbolic_atom_iterator_t it_atoms, ie_atoms;
    string_buffer_t buf = {NULL, 0};
    clingo_control_symbolic_atoms(ctl, &atoms);
    clingo_symbolic_atoms_begin(atoms, NULL, &it_atoms);
    clingo_symbolic_atoms_end(atoms, &ie_atoms);

    for (;;) {
        bool equal, fact, external;
        clingo_symbol_t symbol;
        char *predicate;
        clingo_symbolic_atoms_iterator_is_equal_to(atoms, it_atoms, ie_atoms, &equal);

        // check if we are at the end of the sequence
        if (equal)
            break;
        // get the associated symbol
        clingo_symbolic_atoms_symbol(atoms, it_atoms, &symbol);
        get_symbol_string(symbol, &buf);
        // determine if the atom is fact or external
        clingo_symbolic_atoms_is_fact(atoms, it_atoms, &fact);
        clingo_symbolic_atoms_is_external(atoms, it_atoms, &external);
        con->atoms.push_back(symbol);
        assert(buf.string);
        predicate = (char *)malloc(sizeof(char) * buf.string_n);
        strcpy(predicate, buf.string);
        con->atom_symbol_map[symbol] = std::string(predicate);
        // printf("Inside get_symbol_atoms %lu %s.\n", symbol, buf.string);

        if (!fact && !external) {
            con->active_atoms.push_back(symbol);
            if (problem.independent_sup_symbols.find(std::string(predicate)) != problem.independent_sup_symbols.end()) {
                con->active_atoms_ind_sup.push_back(symbol);
            }
        }
        // advance the next element in the sequence
        clingo_symbolic_atoms_next(atoms, it_atoms, &it_atoms);
    }
    std::cout << "Active atoms (independent support): " << con->active_atoms.size() << " (" << con->active_atoms_ind_sup.size() << ")";
    if (problem.use_ind_sup) {
        std::cout << std::endl;
        std::cout << "c Using independent support from " << problem.independent_set; 
    }
}

void print_all(Configuration *con)
{
    std::cout << " Atom and symbol mapping ==========\n";
    for (auto itr = con->atom_symbol_map.begin(); itr != con->atom_symbol_map.end(); itr++) {
        std::cout << "Atom: " << itr->first << " symbol: " << itr->second << "\n";
    }
    std::cout << " Active atoms ==========\n";
    for (auto e: con->active_atoms)
        std::cout << e << "\n";
}

void generate_k_xors(unsigned k, Configuration *con)
{
    assert(k >= con->xor_cons.size());
    srand(con->seed);
    //srand(0);
    int xor_generated = k - con->xor_cons.size();
    for (int i = 0; i < xor_generated; i++) {
        XOR new_xor;
        if (problem.use_ind_sup)
            new_xor.literals = selectKItems(con->active_atoms_ind_sup);
        else
            new_xor.literals = selectKItems(con->active_atoms);
        new_xor.rhs = rand() % 2;
        // std::cout << "new_xor.rhs: " << new_xor.rhs << std::endl;
        con->xor_cons.push_back(new_xor);
    }
    printf("\n");
    assert(k == con->xor_cons.size());
}
void add_execution_time(clingo_control_t *ctl, Configuration *con)
{
    assert(ctl);
    const clingo_statistics_t *stats;
    uint64_t stats_key, key, subkey;
    clingo_statistics_type_t type;
    char const *name;
    double exec_time;

    clingo_control_statistics(ctl, &stats);
    clingo_statistics_root(stats, &stats_key);
    clingo_statistics_type(stats, stats_key, &type);
    // assert((enum clingo_statistics_type)type == clingo_statistics_type_map);

    // summary is at index 2
    key = stats_key;
    clingo_statistics_map_subkey_name(stats, key, 2, &name);
    assert(string(name) == string("summary"));
    clingo_statistics_map_at(stats, key, name, &subkey);
    clingo_statistics_type(stats, subkey, &type);
    // assert((enum clingo_statistics_type)type == clingo_statistics_type_map);

    // summary is at index 7
    key = subkey;
    clingo_statistics_map_subkey_name(stats, key, 7, &name);
    // assert(strcmp(name, "times") == 0);
    clingo_statistics_map_at(stats, key, name, &subkey);
    clingo_statistics_type(stats, subkey, &type);
    // assert((enum clingo_statistics_type)type == clingo_statistics_type_map);

    // summary is at index 7
    key = subkey;
    clingo_statistics_map_subkey_name(stats, key, 1, &name);
    // assert(strcmp(name, "cpu") == 0);
    clingo_statistics_map_at(stats, key, name, &subkey);
    clingo_statistics_type(stats, subkey, &type);
    // assert((enum clingo_statistics_type)type == clingo_statistics_type_value);
    clingo_statistics_value_get(stats, subkey, &exec_time);
    // we get execution time and appended with clasp's time
    con->time_in_clasp = con->time_in_clasp + exec_time;
}

std::string get_parity_predicate(string term, int xor_id, int parity)
{
    assert(parity == 0 || parity == 1);
    std::string pred = "__parity(" + std::to_string(xor_id) + ", ";
    if (parity)
        pred += "odd";
    else
        pred += "even";

    if (!term.empty()) {
        pred += ", " + (std::string)term + ") :- " + (std::string)term + ". ";
    } else {
        pred += "). ";
    }
    return pred;
}

std::string get_parity(int parity)
{
    assert(parity == 0 || parity == 1);
    std::string pred = "";
    if (parity)
        pred += "&odd{ ";
    else
        pred += "&even{ ";
    return pred;
}

void translation(
    clingo_control_t **ctl,
    Configuration *con,
    bool debug,
    std::ostream &debug_file,
    std::ostream &xorro_file,
    unsigned start,
    int end
) {
    //write "test_parity.txt"
    std::ofstream myfile;
    myfile.open("test_parity.txt");
    if (end == -1)
        end = con->xor_cons.size();
    assert(start <= end);
    assert(start >= 1 && end <= con->xor_cons.size());
    auto start_itr = con->xor_cons.begin() + start - 1;
    auto end_itr = con->xor_cons.begin() + end;
    std::string string_added;
    std::string string_added_xorro;
    while (start_itr != end_itr) {
        bool parity = (*start_itr).rhs;
        auto terms = (*start_itr).literals;
        auto start_term = terms.begin();
        string_added += get_parity_predicate("", start - 1, (int)parity);
        string_added_xorro += get_parity((int) parity);
        while (start_term != terms.end()) {
            string term = atom_to_symbol(*start_term, con);
            std::string temp = get_parity_predicate(term, start - 1, (int)parity);
            string_added += temp;
            string_added_xorro += (term + ":" + term);
            if (start_term + 1 == terms.end()) {
                string_added_xorro += "}. ";
            }
            else {
                string_added_xorro += ";";
            }
            myfile << temp << std::endl;
            start_term++;
        }
        start++;
        start_itr++;
    }
    // parity constraints are adding as normal rule
    myfile << string_added << std::endl;
    myfile.close();

    if (debug) {
        xorro_file << string_added << std::endl;
        debug_file << string_added_xorro << std::endl;
        std::string condition;
        condition =
            ":- { __parity(ID,even,X) } = N, N\\2!=0, __parity(ID,even).  \
            :- { __parity(ID,odd ,X) } = N, N\\2!=1, __parity(ID,odd).";
        xorro_file << condition << std::endl;
    }
    clingo_control_add(*ctl, "base", NULL, 0, string_added.c_str());
}
