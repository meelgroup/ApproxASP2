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


#ifndef UTILITY_H_
#define UTILITY_H_
#include "iterations.h"
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
#include <set>

// char const *error_message;
// int ret = 0;
using std::string;
struct SATCount
{
uint32_t hashCount;
uint32_t cellSolCount;
};

typedef struct xor_constraint {
std::vector<clingo_symbol_t> literals;
bool rhs;
} XOR;

typedef struct program {
double conf;
double tol;
int thresh;
int t;
int interval;
unsigned timeout;
std::vector<float> confidences;

std::string asp_file;
std::string independent_set;
bool use_sparse;
std::string parity_string;
std::vector<std::string> xor_parity_string;
char* input_file;

const char** asp_argument;
int argu_count;
int seed;

bool use_ind_sup = false;
std::vector<clingo_symbol_t> atoms;
std::vector<clingo_symbol_t> active_atoms;
std::vector<clingo_symbol_t> active_atoms_ind_sup;
std::set<std::string> independent_sup_symbols;
std::unordered_map<clingo_symbol_t, string> atom_symbol_map;	
std::unordered_map<clingo_literal_t, clingo_symbol_t> literal_atom_map;
const Constants constants;
unsigned number_of_active_atoms;

std::vector<XOR> xor_cons;
std::vector<int> independent_support;

unsigned xor_last_added;

double time_in_clasp;
unsigned clasp_call;
unsigned clasp_call_timeout;
double gauss_propagate_time = 0;
double gauss_check_time = 0;
double clingo_assignment_time = 0;
int clingo_assignment_called = 0;
double clingo_add_clause_time = 0;
int clingo_add_clause_called = 0;
} Configuration;

typedef struct string_buffer {
char *string;
size_t string_n;
} string_buffer_t;

struct SparseData {
    explicit SparseData(int _table_no) :
        table_no(_table_no)
    {}

    uint32_t next_index = 0;
    double sparseprob = 0.5;
    int table_no = -1;
};

int compute_pivot(float xi, double thresh);
int compute_iteration(Configuration *con);
float in_range(char const *label, float conf);
float confidence(char const *label, float value);
float tolerance(char const *label, float value);
unsigned iteration_count(char const *label, float value);
void get_symbol_string(clingo_symbol_t symbol, string_buffer_t *buf);
void reset_Configuration(Configuration *con);
string atom_to_symbol(clingo_symbol_t atom, Configuration *con);
std::vector<clingo_symbol_t> selectKItems(std::vector<clingo_symbol_t> stream);
void get_symbol_atoms(clingo_control_t *ctl, Configuration *con);
void print_all(Configuration *con);
void generate_k_xors(unsigned k, Configuration *con, SparseData& sparse_data);
void add_execution_time(clingo_control_t *ctl, Configuration *con);
std::string get_parity_predicate(string term, int xor_id, int parity);
std::string get_parity_string(Configuration *con, int m_value);
void translation(
    clingo_control_t **ctl,
    Configuration *con,
    bool debug,
    std::ostream &debug_file,
    unsigned start,
    int end
);
int find_best_sparse_match(Configuration *con);

#endif //UTILITY_H_