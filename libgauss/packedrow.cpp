/******************************************
Copyright (c) 2018  Mate Soos
Copyright (c) 2012  Cheng-Shen Han
Copyright (c) 2012  Jie-Hong Roland Jiang

For more information, see " When Boolean Satisfiability Meets Gaussian
Elimination in a Simplex Way." by Cheng-Shen Han and Jie-Hong Roland Jiang
in CAV (Computer Aided Verification), 2012: 410-426


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

#include "packedrow.h"
#include <cstdint>

// using namespace CMSat;

bool PackedRow::fill(
    vec<Lit>& tmp_clause,
    const vec<lbool>& assigns,
    const vector<uint32_t>& col_to_var_original
) const
{
    bool final = !rhs_internal;

    tmp_clause.clear();
    uint32_t col = 0;
    bool wasundef = false;
    for (uint32_t i = 0; i < size; i++) for (uint32_t i2 = 0; i2 < 64; i2++) {
        if ((mp[i] >> i2) &1) {
            const uint32_t& var = col_to_var_original[col];
            assert(var != std::numeric_limits<uint32_t>::max());

            const lbool val = assigns[var];
            const bool val_bool = val == l_True;
            tmp_clause.push(Lit(var, val_bool));
            final ^= val_bool;
            if (val == l_Undef) {
                assert(!wasundef);
                Lit tmp(tmp_clause[0]);
                tmp_clause[0] = tmp_clause.last();
                tmp_clause.last() = tmp;
                wasundef = true;
            }
        }
        col++;
    }
    if (wasundef) {
        tmp_clause[0] ^= final;
        //assert(ps != ps_first+1);
    } else
        assert(!final);

    return wasundef;
}

///returns popcnt
uint32_t PackedRow::find_watchVar(
    vector<int32_t>& tmp_clause,
    const vector<uint32_t>& col_to_var,
    vec<bool> &GasVar_state,
    uint32_t& nb_var
) {
    uint32_t  tmp_var = 0;
    uint32_t popcnt = 0;
    nb_var = std::numeric_limits<uint32_t>::max();
    uint32_t i;
    tmp_clause.clear();


    for(i = 0; i < size*64; i++) {
        if (this->operator[](i)){
            popcnt++;
            tmp_var = col_to_var[i];
            // tmp_clause.push_back(Lit(tmp_var, false));
            tmp_clause.push_back(tmp_var);
            if( !GasVar_state[tmp_var] ){  //nobasic
                nb_var = tmp_var;
                break;
            }else{  // basic
                // Lit tmp(tmp_clause[0]);
                int32_t tmp = tmp_clause[0];
                tmp_clause[0] = tmp_clause.back();
                tmp_clause.back() = tmp;
            }
        }
    }

    for( i = i + 1 ; i <  size*64; i++) {
        if (this->operator[](i)){
            popcnt++;
            tmp_var = col_to_var[i];
            // tmp_clause.push_back(Lit(tmp_var, false));
            tmp_clause.push_back(tmp_var);
            if( GasVar_state[tmp_var] ){  //basic
                // Lit tmp(tmp_clause[0]);
                int32_t tmp = tmp_clause[0];
                tmp_clause[0] = tmp_clause.back();
                tmp_clause.back() = tmp;
            }
        }
    }
    assert(tmp_clause.size() == popcnt);
    assert( popcnt == 0 || GasVar_state[ tmp_clause[0] ]) ;
    return popcnt;

}

inline int scan_fwd_64b(uint64_t value)
{
    return  __builtin_ffsll(value);
}

gret PackedRow::checkGause(
    vector<int32_t>& tmp_clause,
    const vector<lbool>& assigns,
    const vector<uint32_t>& col_to_var,
    vec<bool> &GasVar_state, // variable state  : basic or non-basic
    PackedRow& tmp_col,
    PackedRow& tmp_col2,
    PackedRow& cols_vals,
    PackedRow& cols_unset
) {

    uint32_t pop = tmp_col.set_and_until_popcnt_atleast2(*this, cols_unset);

    if (pop >= 2) {
        return gret::nothing_fnewwatch;
    }

    bool final = !rhs_internal;
    
    tmp_clause.clear();

    for (uint32_t i = 0; i != size; i++) if (mp[i]) {
        uint64_t tmp = mp[i];
        for (uint32_t i2 = 0 ; i2 < 64; i2++) {
            if(tmp & 1){
                const uint32_t var = col_to_var[i * 64  + i2];
                lbool val = l_Undef;
                if (!cols_unset[i * 64  + i2]) {
                    if (cols_vals[i * 64  + i2]) {
                        val = l_True;
                    }
                    else {
                        val = l_False;
                    }
                }
                // const lbool val = assigns[var];
                // if (unassigned_literal >= 2 && val == l_Undef && !GasVar_state[var]) {  // find non basic value
                //     nb_var = var;
                //     return gret::nothing_fnewwatch; // nothing
                // }
                const bool val_bool = (val == l_True);
                final ^= val_bool;
                tmp_clause.push_back(var);
                if (val_bool) 
                    tmp_clause.back() = -tmp_clause.back();
                // tmp_clause.push_back(Lit(var, val_bool));
                // if (unassigned_literal == 1 && val == l_Undef) {
                //     std::swap(tmp_clause[0], tmp_clause.back());
                // }
                if (val == l_Undef) {
                    std::swap(tmp_clause[0], tmp_clause.back());
                }
            }
            tmp >>= 1;
        }
    }

    // for ( uint32_t i =0; i != start/64; i++) if (likely(mp[i])) {
    //     uint64_t tmp = mp[i];
    //     for (uint32_t i2 = 0 ; i2 < 64; i2++) {
    //         if(tmp & 1){
    //             const uint32_t var = col_to_var[i * 64  + i2];
    //             const lbool val = assigns[var];
    //             if (unassigned_literal >= 2 && val == l_Undef &&  !GasVar_state[var] ){  // find non basic value
    //                 nb_var = var;
    //                 return gret::nothing_fnewwatch;   // nothing
    //             }
    //             const bool val_bool = val == l_True;
    //             final ^= val_bool;
    //             tmp_clause.push_back(Lit(var, val_bool));
    //             if (unassigned_literal == 1 && val == l_Undef) {
    //                 std::swap(tmp_clause[0], tmp_clause.back());
    //             }
    //         }
    //         tmp >>= 1;
    //     }
    // }
    assert(pop <= 1);
    if (pop == 1) {    // propogate
        if (final)
            tmp_clause[0] = -tmp_clause[0];
        return gret::prop;  // propogate
    } else if (!final) {
        return gret::confl;  // conflict
    }
    // this row already true
    return gret::nothing;  // nothing

}

gret PackedRow::propGause(
    vector<int32_t>& tmp_clause,
    const vector<lbool>& assigns,
    const vector<uint32_t>& col_to_var,
    vec<bool> &GasVar_state, // variable state  : basic or non-basic
    uint32_t& nb_var,
    uint32_t start,
    PackedRow& tmp_col,
    PackedRow& tmp_col2,
    PackedRow& cols_vals,
    PackedRow& cols_unset
) {

    uint32_t pop = tmp_col.set_and_until_popcnt_atleast2(*this, cols_unset);
    nb_var = std::numeric_limits<uint32_t>::max();
    if (pop >= 2) {
        for (int i = 0; i < size; i++) if (tmp_col.mp[i]) {
            int64_t tmp = tmp_col.mp[i];
            unsigned long at;
            at = scan_fwd_64b(tmp);
            int extra = 0;
            while (at != 0) {
                uint32_t col = extra + at-1 + i*64;
                #ifdef SLOW_DEBUG
                assert(tmp_col[col] == 1);
                #endif
                const uint32_t var = col_to_var[col];

                #ifdef SLOW_DEBUG
                const lbool val = assigns[var];
                assert(val == l_Undef);
                #endif

                // found new non-basic variable, let's watch it
                if (!GasVar_state[var]) {
                    nb_var = var;
                    return gret::nothing_fnewwatch;
                }

                extra += at;
                if (extra == 64)
                    break;

                tmp >>= at;
                at = scan_fwd_64b(tmp);
            }
        }
        assert(false && "Should have found a new watch!");
    }

    bool final = !rhs_internal;
    
    tmp_clause.clear();
    start = 0;
    for (uint32_t i = start/64; i != size; i++) if (mp[i]) {
        uint64_t tmp = mp[i];
        for (uint32_t i2 = 0 ; i2 < 64; i2++) {
            if(tmp & 1){
                const uint32_t var = col_to_var[i * 64  + i2];
                lbool val = l_Undef;
                if (!cols_unset[i * 64  + i2]) {
                    if (cols_vals[i * 64  + i2]) {
                        val = l_True;
                    }
                    else {
                        val = l_False;
                    }
                }
                // const lbool val = assigns[var];
                // if (unassigned_literal >= 2 && val == l_Undef && !GasVar_state[var]) {  // find non basic value
                //     nb_var = var;
                //     return gret::nothing_fnewwatch; // nothing
                // }
                const bool val_bool = (val == l_True);
                final ^= val_bool;
                tmp_clause.push_back(var);
                if (val_bool) {
                    tmp_clause.back() = -tmp_clause.back();
                }
                // tmp_clause.push_back(Lit(var, val_bool));
                // if (unassigned_literal == 1 && val == l_Undef) {
                //     std::swap(tmp_clause[0], tmp_clause.back());
                // }
                if (val == l_Undef) {
                    std::swap(tmp_clause[0], tmp_clause.back());
                }
            }
            tmp >>= 1;
        }
    }

    // for ( uint32_t i =0; i != start/64; i++) if (likely(mp[i])) {
    //     uint64_t tmp = mp[i];
    //     for (uint32_t i2 = 0 ; i2 < 64; i2++) {
    //         if(tmp & 1){
    //             const uint32_t var = col_to_var[i * 64  + i2];
    //             const lbool val = assigns[var];
    //             if (unassigned_literal >= 2 && val == l_Undef &&  !GasVar_state[var] ){  // find non basic value
    //                 nb_var = var;
    //                 return gret::nothing_fnewwatch;   // nothing
    //             }
    //             const bool val_bool = val == l_True;
    //             final ^= val_bool;
    //             tmp_clause.push_back(Lit(var, val_bool));
    //             if (unassigned_literal == 1 && val == l_Undef) {
    //                 std::swap(tmp_clause[0], tmp_clause.back());
    //             }
    //         }
    //         tmp >>= 1;
    //     }
    // }
    assert(pop <= 1);
    if (pop == 1) {    // propogate
        if (final)
            tmp_clause[0] = -tmp_clause[0];
        // tmp_clause[0] = tmp_clause[0].unsign()^final;
        return gret::prop;  // propogate
    } else if (!final) {
        return gret::confl;  // conflict
    }
    // this row already true
    return gret::nothing;  // nothing

}

void PackedRow::degug_propGause(const vector<lbool>& assigns, const vector<uint32_t>& col_to_var, int& unassigned, bool& conflict) {
    int start = 0;
    unassigned = 0;
    conflict = rhs_internal;
    unassigned = 0;
    int true_assigned = 0; 
    for (uint32_t i = start/64; i != size; i++) if (mp[i]) {
        uint64_t tmp = mp[i];
        for (uint32_t i2 = 0 ; i2 < 64; i2++) {
            if(tmp & 1){
                const uint32_t var = col_to_var[i * 64  + i2];
                #ifdef PREVIOUS_ASSIGN
                const lbool val = assigns[var];
                if (val == l_Undef) {  // find non basic value
                    unassigned++;
                }
                else if (val == l_True) {
                    true_assigned++; 
                }
                #endif
            }
            tmp >>= 1;
        }
    }
    conflict = ((true_assigned % 2) != rhs_internal);   
    // cout << "True_assigned: " << true_assigned << " " << "Unassigned: " << unassigned << " RHS internal: " << rhs_internal << endl;
}

gret PackedRow::propGause_debug(
    vector<int32_t>& tmp_clause,
    const vector<lbool>& assigns,
    const vector<uint32_t>& col_to_var,
    vec<bool> &GasVar_state, // variable state  : basic or non-basic
    uint32_t& nb_var,
    uint32_t start
) {

    bool final = !rhs_internal;
    cout << "[ "; 
    nb_var = std::numeric_limits<uint32_t>::max();
    tmp_clause.clear();

    for (uint32_t i = start/64; i != size; i++) if (mp[i]) {
        uint64_t tmp = mp[i];
        for (uint32_t i2 = 0 ; i2 < 64; i2++) {
            if(tmp & 1){
                const uint32_t var = col_to_var[i * 64  + i2];
                const lbool val = assigns[var];
                if (val == l_Undef && !GasVar_state[var]) {  // find non basic value
                    nb_var = var;
                    return gret::nothing_fnewwatch; // nothing
                }
                const bool val_bool = (val == l_True);
                final ^= val_bool;
                tmp_clause.push_back(var);
                if (val_bool) {
                    tmp_clause.back() = -tmp_clause.back();
                }
                string tmp = (int) Lit(var, val_bool).sign() ? "" : "-";
                cout << Lit(var, val_bool).var() << " ";
                if (likely(GasVar_state[var])) {
                    std::swap(tmp_clause[0], tmp_clause.back());
                }
            }
            tmp >>= 1;
        }
    }

    for ( uint32_t i =0; i != start/64; i++) if (likely(mp[i])) {
        uint64_t tmp = mp[i];
        for (uint32_t i2 = 0 ; i2 < 64; i2++) {
            if(tmp & 1){
                const uint32_t var = col_to_var[i * 64  + i2];
                const lbool val = assigns[var];
                if (val == l_Undef &&  !GasVar_state[var] ){  // find non basic value
                    nb_var = var;
                    return gret::nothing_fnewwatch;   // nothing
                }
                const bool val_bool = val == l_True;
                final ^= val_bool;
                tmp_clause.push_back(var);
                if (val_bool) {
                    tmp_clause.back() = -tmp_clause.back();
                }
                
                cout << Lit(var, val_bool).var() << " ";
                if ( GasVar_state[var] ) {
                    std::swap(tmp_clause[0], tmp_clause.back());
                }
            }
            tmp >>= 1;
        }
    }
    cout << "|" << rhs_internal << " ]";
    if (assigns[abs(tmp_clause[0])] == l_Undef) {    // propogate
        if (final) {
            tmp_clause[0] = -tmp_clause[0];
        }
        return gret::prop;  // propogate
    } else if (!final) {
        cout << " <- conflict" << endl;
        return gret::confl;  // conflict
    }
    // this row already true
    cout << " <- ok" << endl;
    return gret::nothing;  // nothing

}



