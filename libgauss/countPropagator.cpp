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

/**
This is the simples XOR reasoning propagator one could build, because in fact, is not a propagator.
In other words, it does not interfere with clasp's propagation. 
It simply waits for all the literals to be assigned, and check (by counting) if the parity constraint holds.
If not, add the respective nogood/clause.

The propagator monitors __parity/2 and __parity/3 atoms to build the corresponding XORs state
These atoms also help to dectect: 
- top-level conflicts such as empty odd XOR*
- unary XORs that are needed to pass as consequences*
- empty even XOR constraint can be safely removed
- unit propagation or GJE as a preprocessing step to simplify or reduce the constraints

 TODO
- Thread safe
- Check XORs satisfiability as a preprocessing step* 
- Propagate unary XORs (consequences) at decision level zero*
- XORs preprocessing. Always in normal form
  - positive literals. a xor not b = a xor b xor true
  - no repeated literals. a xor a xor b xor c = b xor c

  * These cases might not be possible here because this propagator is configured to visit the check method on total assignments only. 
  In another XOR approach, these are a must have. 
 */

#include <clingo.h>
#include "xor.h"
#include "utility.h"
#include "countPropagator.h"

using std::vector;

// Global variable
bool display = false;

/*
Get the numeric arguments from each __parity atom
*/
bool get_arg(clingo_symbol_t sym, int offset, int *num)
{
    clingo_symbol_t const *args;
    size_t args_size;
    // get the arguments of the function symbol
    if (!clingo_symbol_arguments(sym, &args, &args_size)) { return false; }
    // get the requested numeric argument
    if (!clingo_symbol_number(args[offset], num)) { return false; }

    return true;
}

/*
Get the arguments from each __parity atom in string form. Used for the parity (odd or even) and for conditional literals
*/
clingo_symbol_t get_arg_str(clingo_symbol_t sym, int offset, char **str_argu)
{
    clingo_symbol_t const *args;
    size_t args_size;
    // get the arguments of the function symbol
    if (!clingo_symbol_arguments(sym, &args, &args_size)) { return false; }
    // get the requested numeric argument
    string_buffer_t buf = {NULL, 0};
    get_symbol_string(args[offset], &buf);
    *str_argu = (char *)malloc((buf.string_n) * sizeof(char));
    strcpy(*str_argu, buf.string);
    return args[offset];
}

/*
Init function. 
 */
bool init(clingo_propagate_init_t *init, propagator_t *data)
{
	if (display)
		printf("\nInit Function.\n");

	// Set the call of the check method on total assingments only.
	// For other XOR approaches, change the check mode to clingo_propagator_check_mode_fixpoint
	clingo_propagate_init_set_check_mode(init, clingo_propagator_check_mode_total);

	// TODO
	// Solver state handling per thread
    //size_t threads = clingo_propagate_init_number_of_threads(init);
	// ensure that solve can be called multiple times
	// for simplicity, the case that additional holes or pigeons to assign are grounded is not handled here
	/*if (data->states != NULL) {
		// in principle the number of threads can increase between solve calls by changing the configuration
		// this case is not handled (elegantly) here
		if (threads > data->states_size) {
			clingo_set_error(clingo_error_runtime, "more threads than states");
		}
		return true;
	}*/
	// allocate memory for exactly one state per thread
	/*if (!(data->states = (state_t*)malloc(sizeof(*data->states) * threads))) {
		clingo_set_error(clingo_error_bad_alloc, "allocation failed");
		return false;
	}
	memset(data->states, 0, sizeof(*data->states) * threads);
	data->states_size = threads;
	*/

	// Defines
	const clingo_symbolic_atoms_t *atoms;
    clingo_signature_t signature; // For atom's arity
    clingo_symbolic_atom_iterator_t atoms_it, atoms_ie;
    string_buffer_t buffer= {NULL, 0};
	// XORs' vector
    vector<Xor> xorClauses;
	// XORs' parities
    //vector<bool> xorParity; // Not used in this propagator but useful in others.
	// XORs' IDs
	vector<int> xorIDs;

	// for now we only care for __parity/3 atoms
    // first get the symbolic atoms handle
    if (!clingo_propagate_init_symbolic_atoms(init, &atoms)) { return false; }
    // create parity/2 signature to filter symbolic atoms with
    if (!clingo_signature_create("__parity", 2, true, &signature)) { return false; }
    // get an iterator after the last __parity/2 atom
    // (atom order corresponds to grounding order (and is unpredictable))
    if (!clingo_symbolic_atoms_end(atoms, &atoms_ie)) { return false; }
    // loop over the __parity/2 atoms
    if (!clingo_symbolic_atoms_begin(atoms, &signature, &atoms_it)) { return false; }

	// Defines
    char *parity; // Our parity
    int xor_count = 0; // Counting how many XORs we have
	int id; // XOR ID
	bool equal; // Break condition
	clingo_symbol_t symbolyc_atom; // Clingo's Symbolic Atoms
		
    while (true) {
        
        // stop iteration if the end is reached
        if (!clingo_symbolic_atoms_iterator_is_equal_to(atoms, atoms_it, atoms_ie, &equal)) { return false; }
        if (equal) { break; }
        // extract the symbols from the atom
        if (!clingo_symbolic_atoms_symbol(atoms, atoms_it, &symbolyc_atom)) { return false; }

		// Get the XOR ID
        get_arg(symbolyc_atom, 0, &id);
		xorIDs.push_back(id); // push the ids from each given/generated XOR
		// Get the parity
        get_arg_str(symbolyc_atom, 1, &parity);
		// Break if the parities are misspelled
        assert(!strcmp(parity, "odd") || !strcmp(parity, "even")); // Safety check
		// Get the atom
		get_symbol_string(symbolyc_atom, &buffer);//Not necessary but only for visualization. This does not contribute to the propagator
		if (display)
			printf("get_symbol_string: %s.\n", buffer.string); 
		xor_count++;

        // advance to the next placement atom
        if (!clingo_symbolic_atoms_next(atoms, atoms_it, &atoms_it)) { return false; }
    }

	// Also, for visualization only
	if (display){
		printf("Total XOR constraints: %d.\n", xor_count);
		for (auto &xorID : xorIDs){
			printf("xor ID: %d\n", xorID);
		}
	}

	// Now, iterate over each XOR to get their respective solver literals
	// TODO: Identify which XORs are empty. Again, empty even must be removed, empty odd yields UNSAT
    if (!clingo_signature_create("__parity", 3, true, &signature)) { return false; }
    // get an iterator after the last __parity/3 atom
    // (atom order corresponds to grounding order (and is unpredictable))
    if (!clingo_symbolic_atoms_end(atoms, &atoms_ie)) { return false; }
	// Iterate over the __parity/3 atoms
	if (display)
		printf("\n");

	for(int i = 0; i < xor_count; i++){
		if (display)
			printf("xor ID: %d\n", xorIDs[i]);
		vector<uint32_t> lits;
		lits.clear();
		xorClauses.clear();

		// Break if there are no atoms with the given signature
		if (!clingo_symbolic_atoms_begin(atoms, &signature, &atoms_it)) { return false; }
	
		char *condition; // Conditional literal. Usually on XORs coming from theory atoms, we have:
		// &odd{ t : c}. where t is a Term and c is the Conditional Literal.
		clingo_literal_t lit, solver_literal; // Get the literal from ASPIF and the solver literal
		clingo_symbol_t symbolyc_atom; // Clingo's symbolic atoms
		bool even = false; // Check if there is an even XOR
		int id; // XOR ID
		bool equal; // Break condition
			
		while (true) {

			// stop iteration if the end is reached
			if (!clingo_symbolic_atoms_iterator_is_equal_to(atoms, atoms_it, atoms_ie, &equal)) { return false; }
			if (equal) { break; }
			if (!clingo_symbolic_atoms_symbol(atoms, atoms_it, &symbolyc_atom)) { return false; }
			// get the solver literal for the placement atom
			if (!clingo_symbolic_atoms_literal(atoms, atoms_it, &lit)) { return false; }
			if (!clingo_propagate_init_solver_literal(init, lit, &solver_literal)) { return false; }

			// Get the XOR ID symbol by index
			get_arg(symbolyc_atom, 0, &id);
			// Check the IDs. The IDs not necessarily are consecutive.
			// TODO: Here we can identify emtpy XORs
			if (id == xorIDs[i]){ 
				get_arg_str(symbolyc_atom, 1, &parity);
				symbolyc_atom = get_arg_str(symbolyc_atom, 2, &condition); // This is just called to print the condition. It does not contribute to the propagator
				if (display)
					printf("id: %d, solver literal: %d : condition: %s parity: %s \n", id, solver_literal, condition, parity);
				if (!strcmp(parity, "even")){ even = true; }
				lits.push_back(solver_literal);
			}
			// Break if the parities are misspelled
			assert(!strcmp(parity, "odd") || !strcmp(parity, "even"));
			
			// advance to the next placement atom
			if (!clingo_symbolic_atoms_next(atoms, atoms_it, &atoms_it)) { return false; }
		}
		/* XORs equivalences.
		   For this simple approach, we do not need to keep a separate data structure for the parity.
		   On the other hand, all XORs must respect the odd parity. 
		   An even XOR is strongly equivalent to an odd XOR containing an uneven number of negated literals.
		   For example: &even{a}. = &odd{not a}. In other words, a xor true = -a xor false
		   In this matter, we just simply negate the first literal in case it is an even XOR.
		 */
		if (even){ lits[0] = -lits[0]; }

		if (display)
		{	  	
			printf("Adding XOR to the state");
			for(int i=0; i < lits.size(); ++i){
				printf("%d ", lits[i]);
			}
			printf("\n");
		}

		// Create XORs
		xorClauses.push_back(Xor(lits, even));
		// Add XORs to state
		data->xorState.push_back(xorClauses);

		// Finish symbolic atoms iteration
		if (!clingo_symbolic_atoms_end(atoms, &atoms_ie)) { return false; }
	}
	if (display)
		printf("\n");
	
    return true;
}
/*
Check function. 
 */

bool check(clingo_propagate_control_t *control, propagator_t *data)
{
	if (display)
		printf("\nCheck Function.\n");

	// Get clingo assignment and truth's value
	const clingo_assignment_t *assignment = clingo_propagate_control_assignment(control);
	clingo_truth_value_t value;

	// For each XOR in the state
	for (auto state : data->xorState) {
		for (auto xorClauses : state){
			int count = 0; // truth assignments counter
			vector<uint32_t> clause; 
			clause.clear();
			for (auto lit : xorClauses){
				if (display)
					printf("%d ",lit);
				// Get the current assignment
				clingo_assignment_truth_value(assignment, lit, &value);		   
				switch (value)
				{
				case clingo_truth_value_true: // If true
					if (display)
						printf("true \n");
					count++; // Increase the counter
					clause.push_back(lit);
					break;
				case clingo_truth_value_false: // If false
					if (display)
						printf("false \n");
					clause.push_back(-lit);
					break;
				default:
					break;
				}
			}			
			if (!(count % 2 == 1)) // Check if the odd XOR is satisfied...
			{
				if (display){				
					printf("conflict... add nogood \n");
					for (auto lit : clause)
						printf("%d ",lit);
					printf("\n");
				}

				// Definetely, there must be a more elegant and proper way to do this...
				/*
				  ASP has the concept of a nogood as an unvalid assignment or as a constraint. Something that is not allowed to happen.
				  Formally, a nogood is equivalent to a clause with all literals negated.
				  A nogood of is equivalent to clause([-lit for lit in clause])
				 */
				clingo_literal_t nogood[clause.size()];
				bool result; // Condition to stop propagation
				for (int i = 0; i < clause.size(); i++ ) {
					nogood[i] = -clause[i];
				}
				// Add nogood
				auto size = sizeof(nogood)/sizeof(*nogood);
				if (!clingo_propagate_control_add_clause(control, nogood, size, clingo_clause_type_learnt , &result)) { return false; }
				if (!result) { return true; }
				// Propagate the consequences
				if (!clingo_propagate_control_propagate(control, &result)) { return false; }
				if (!result) { return true; }
			}
		}
		if (display)
			printf("\n");
    }
    return true;
}
