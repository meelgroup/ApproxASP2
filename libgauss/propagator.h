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


#ifndef PROPAGATOR_H_
#define PROPAGATOR_H_
#include <clingo.h>
#include <unordered_map>
#include "xor.h"
#include "gqueuedata.h"
#include "EGaussian.h"
#include "solverstate.h"

using std::vector;

// state information for the propagator
typedef struct {
// mapping from solver literals capturing pigeon placements to hole numbers
// (solver literal -> hole number or zero)
vector<GaussQData> gqueuedata;
vector<EGaussian*> gmatrixes;
SolverState* solver;

} propagator_t;

extern Configuration problem;

bool init_all_matrixes(propagator_t *prop);
bool get_arg(clingo_symbol_t sym, int offset, int *num);
clingo_symbol_t get_arg_str(clingo_symbol_t sym, int offset, char **str_argu);
void clearEnGaussMatrixes(propagator_t *prop);
bool init(clingo_propagate_init_t *init, propagator_t *data);
bool gauss_elimation(clingo_propagate_control_t *control, const clingo_literal_t *changes,
                     size_t size, propagator_t *data);
bool propagate(clingo_propagate_control_t *control, const clingo_literal_t *changes, size_t size,
               propagator_t *data);
bool undo(clingo_propagate_control_t *control, const clingo_literal_t *changes, size_t size,
          propagator_t *data);
bool check(clingo_propagate_control_t *control, propagator_t *data);

#endif //PROPAGATOR_H_