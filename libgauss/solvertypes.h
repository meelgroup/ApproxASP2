/******************************************
Copyright (c) 2016, Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/


#ifndef SOLVERTYPES_H
#define SOLVERTYPES_H

#include "constants.h"

#include <sstream>
#include <algorithm>
#include <limits>
#include <vector>
#include <iostream>
#include <iomanip>
#include <string>
#include <limits>
#include <cassert>
// #include "solverconf.h"  by mahi
// #include "cryptominisat5/solvertypesmini.h"  by mahi

// namespace CMSat {  by mahi

using std::vector;
using std::cout;
using std::endl;
using std::string;

enum class gret{confl, unit_confl, prop, unit_prop, nothing, nothing_fnewwatch};
enum class dret{BACKTRACK, FORWARD, UNCHANGED};

inline std::ostream& operator<<(std::ostream& cout, const dret val)
{
    if (val == dret::BACKTRACK) cout << "BACKTRACK";
    if (val == dret::FORWARD) cout << "FORWARD";
    if (val == dret::UNCHANGED) cout << "UNCHANGED";
    return cout;
}
#endif //SOLVERTYPES_H