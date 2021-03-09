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

// char const *error_message;
// int ret = 0;

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
std::string parity_string;
char* input_file;

const char** asp_argument;
int argu_count;
int seed;

std::vector<clingo_symbol_t> atoms;
std::vector<clingo_symbol_t> active_atoms;
std::unordered_map<clingo_symbol_t, char *> atom_symbol_map;
unsigned number_of_active_atoms;

std::vector<XOR> xor_cons;
std::vector<int> independent_support;

unsigned xor_last_added;

double time_in_clasp;
unsigned clasp_call;
unsigned clasp_call_timeout;
} Configuration;

typedef struct string_buffer {
char *string;
size_t string_n;
} string_buffer_t;

int compute_pivot(float xi);
int compute_iteration(Configuration *con);
float in_range(char const *label, float conf);
float confidence(char const *label, float value);
float tolerance(char const *label, float value);
unsigned iteration_count(char const *label, float value);
void get_symbol_string(clingo_symbol_t symbol, string_buffer_t *buf);
void reset_Configuration(Configuration *con);
char *atom_to_symbol(clingo_symbol_t atom, Configuration *con);
std::vector<clingo_symbol_t> selectKItems(std::vector<clingo_symbol_t> stream);
void get_symbol_atoms(clingo_control_t *ctl, Configuration *con);
void print_all(Configuration *con);
void generate_k_xors(unsigned k, Configuration *con);
void add_execution_time(clingo_control_t *ctl, Configuration *con);
std::string get_parity_predicate(char *term, int xor_id, int parity);
void translation(
    clingo_control_t **ctl,
    Configuration *con,
    bool debug,
    std::ostream &debug_file,
    unsigned start,
    int end
);

#endif //UTILITY_H_