// {{{ MIT License

// Copyright 2021 Flavio Everardo

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
#include "xor.h"
#include <memory>

using std::vector;

// state information for the propagator
typedef struct {
	vector<vector<Xor> > xorState; // Let the state be a vector of XORs
} propagator_t;

bool get_arg(clingo_symbol_t sym, int offset, int *num);
clingo_symbol_t get_arg_str(clingo_symbol_t sym, int offset, char **str_argu);
bool init(clingo_propagate_init_t *init, propagator_t *data);
bool check(clingo_propagate_control_t *control, propagator_t *data);

#endif //PROPAGATOR_H_
