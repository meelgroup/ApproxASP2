#define __STDC_FORMAT_MACROS
#include <clingo.h>
#include <inttypes.h>
#include <sys/stat.h>
#include <iomanip>
#include <iostream>
#include "model_counting.c"
#include "propagator.c"
#include "utility.c"

using std::cout;
using std::endl;
using std::string;

configuration problem;

typedef struct model_buffer {
    clingo_symbol_t *symbols;
    size_t symbols_n;
    char *string;
    size_t string_n;
} model_buffer_t;

void free_model_buffer(model_buffer_t *buf)
{
    if (buf->symbols) {
        free(buf->symbols);
        buf->symbols = NULL;
        buf->symbols_n = 0;
    }

    if (buf->string) {
        free(buf->string);
        buf->string = NULL;
        buf->string_n = 0;
    }
}

bool print_symbol(clingo_symbol_t symbol, model_buffer_t *buf)
{
    bool ret = true;
    char *string;
    size_t n;

    // determine size of the string representation of the next symbol in the model
    if (!clingo_symbol_to_string_size(symbol, &n)) {
        goto error;
    }

    if (buf->string_n < n) {
        // allocate required memory to hold the symbol's string
        if (!(string = (char *)realloc(buf->string, sizeof(*buf->string) * n))) {
            clingo_set_error(clingo_error_bad_alloc,
                             "could not allocate memory for symbol's string");
            goto error;
        }

        buf->string = string;
        buf->string_n = n;
    }

    // retrieve the symbol's string
    if (!clingo_symbol_to_string(symbol, buf->string, n)) {
        goto error;
    }
    cout << buf->string << endl;
    goto out;

error:
    ret = false;

out:
    return ret;
}

bool print_model(clingo_model_t const *model, model_buffer_t *buf, char const *label,
                 clingo_show_type_bitset_t show)
{
    bool ret = true;
    clingo_symbol_t *symbols;
    size_t n;
    clingo_symbol_t const *it, *ie;

    // determine the number of (shown) symbols in the model
    if (!clingo_model_symbols_size(model, show, &n)) {
        goto error;
    }

    // allocate required memory to hold all the symbols
    if (buf->symbols_n < n) {
        if (!(symbols = (clingo_symbol_t *)malloc(sizeof(*buf->symbols) * n))) {
            clingo_set_error(clingo_error_bad_alloc, "could not allocate memory for atoms");
            goto error;
        }

        buf->symbols = symbols;
        buf->symbols_n = n;
    }

    // retrieve the symbols in the model
    if (!clingo_model_symbols(model, show, buf->symbols, n)) {
        goto error;
    }

    printf("%s:", label);

    for (it = buf->symbols, ie = buf->symbols + n; it != ie; ++it) {
        printf(" ");
        if (!print_symbol(*it, buf)) {
            goto error;
        }
    }

    printf("\n");
    goto out;

error:
    ret = false;

out:
    return ret;
}

bool print_solution(clingo_model_t const *model, model_buffer_t *data)
{
    bool ret = true;
    uint64_t number;
    clingo_model_type_t type;
    char const *type_string = "";

    // get model type
    if (!clingo_model_type(model, &type)) {
        goto error;
    }

    switch ((enum clingo_model_type)type) {
        case clingo_model_type_stable_model: {
            type_string = "Stable model";
            break;
        }
        case clingo_model_type_brave_consequences: {
            type_string = "Brave consequences";
            break;
        }
        case clingo_model_type_cautious_consequences: {
            type_string = "Cautious consequences";
            break;
        }
    }

    // get running number of model
    if (!clingo_model_number(model, &number)) {
        goto error;
    }

    printf("%s %" PRIu64 ":\n", type_string, number);

    if (!print_model(model, data, "  shown", clingo_show_type_shown)) {
        goto error;
    }
    if (!print_model(model, data, "  atoms", clingo_show_type_atoms)) {
        goto error;
    }
    if (!print_model(model, data, "  terms", clingo_show_type_terms)) {
        goto error;
    }
    if (!print_model(model, data, " ~atoms",
                     clingo_show_type_complement | clingo_show_type_atoms)) {
        goto error;
    }

    goto out;

error:
    ret = false;

out:
    return ret;
}

bool solve(clingo_control_t *ctl, model_buffer_t *data, clingo_solve_result_bitset_t *result)
{
    bool ret = true;
    int iter = 0;
    clingo_solve_handle_t *handle;
    clingo_model_t const *model;
    uint32_t count = 0;
    // get a solve handle
    if (!clingo_control_solve(ctl, clingo_solve_mode_yield, NULL, 0, NULL, NULL, &handle)) {
        goto error;
    }
    // loop over all models

    while (true) {
        if (!clingo_solve_handle_resume(handle)) {
            goto error;
        }
        if (!clingo_solve_handle_model(handle, &model)) {
            goto error;
        }
        // print the model
        if (model) {
            count++;
            // print_solution(model, data);
        }
        // stop if there are no more models
        else {
            printf("Number of models: %d.\n", count);
            break;
        }
    }
    // close the solve handle
    if (!clingo_solve_handle_get(handle, result)) {
        goto error;
    }

    goto out;

error:
    ret = false;

out:
    // free the solve handle
    return clingo_solve_handle_close(handle) && ret;
}

int main(int argc, char const **argv)
{
    char const *error_message;
    problem.conf = 0.8;
    problem.tol = 0.8;
    problem.interval = 10;
    int ret = 0;
    unsigned thresh, t;
    struct stat buffer;
    clingo_solve_result_bitset_t solve_ret;
    clingo_control_t *ctl = NULL;
    clingo_part_t parts[] = {{"base", NULL, 0}};
    model_buffer_t buf = {NULL, 0, NULL, 0};
    printf("%f, %f, %u.\n", problem.conf, problem.tol, problem.interval);

    int scan = 1;
    char *arg;
    while (scan < argc) {
        unsigned bytes_need = strlen(argv[scan]);
        arg = (char *)malloc(bytes_need * sizeof(char) + 1);
        strcpy(arg, argv[scan]);
        if (!strcmp(arg, "--conf")) {
            problem.conf = confidence(argv[++scan], problem.conf);
        } else if (!strcmp(arg, "--tol")) {
            problem.tol = tolerance(argv[++scan], problem.tol);
        } else if (!strcmp(arg, "--iter")) {
            problem.interval = iteration_count(argv[++scan], problem.interval);
        } else if (!strcmp(arg, "--asp")) {
            problem.asp_file = std::string(argv[++scan]);
        } else if (!strcmp(arg, "--input")) {
            problem.input_file = (char *)malloc(sizeof(char) * (strlen(argv[scan++]) + 1));
            strcpy(problem.input_file, argv[scan]);
        }

        else {
            if (problem.argu_count == 0)
                problem.asp_argument = (const char **)malloc(sizeof(char *));
            else {
                problem.asp_argument = (const char **)realloc(
                    problem.asp_argument, (problem.argu_count + 1) * sizeof(char *));
            }
            // problem.asp_argument[problem.argu_count] = (const char *) malloc( bytes_need * sizeof(char) + 1);
            problem.asp_argument[problem.argu_count] = argv[scan];
            problem.argu_count++;
        }

        free(arg);
        scan++;
    }

    if (problem.asp_file.empty()) {
        cout << "No input file specified" << endl;
        exit(-1);
    } else {
        if (stat(problem.asp_file.c_str(), &buffer) == -1) {
            cout << "No asp file with name: " << problem.asp_file << endl;
            exit(-1);
        }
    }
    if (!problem.input_file) {
        cout << "Approximate counting using file: " << problem.asp_file << "..." << endl;
    } else {
        if (stat(problem.input_file, &buffer) == -1) {
            printf("No input file with name: %s.\n", problem.input_file);
        }
        cout << "Approximate counting using files: " << problem.asp_file << " & "
             << problem.input_file << endl;
    }

    cout << "Approximate counting using confidence " << std::fixed << std::setprecision(2)
         << problem.conf << " and tolerance " << std::fixed << std::setprecision(2) << problem.tol
         << "..." << endl;

    // compute pivot
    problem.thresh = compute_pivot(problem.tol);
    // compute delta
    problem.t = compute_iteration(&problem);
    // setting pivot in clingo control
    if (problem.argu_count == 0)
        problem.asp_argument = (const char **)malloc(sizeof(char *));
    else {
        problem.asp_argument =
            (const char **)realloc(problem.asp_argument, (problem.argu_count + 1) * sizeof(char *));
    }
    char pivot_str[10];
    sprintf(pivot_str, "-n %d", problem.thresh);
    problem.asp_argument[problem.argu_count++] = pivot_str;
    reset_configuration(&problem);
    // register propagator class
    clingo_propagator_t prop = {
        (bool (*)(clingo_propagate_init_t *, void *))init,
        (bool (*)(clingo_propagate_control_t *, clingo_literal_t const *, size_t, void *))propagate,
        (bool (*)(clingo_propagate_control_t *, clingo_literal_t const *, size_t, void *))undo,
        NULL};
    // user data for the propagator
    propagator_t prop_data = {};
    bool debug = true;
    std::ofstream debug_out;

    // Need to test several time
    // scan = 0;
    // printf("problem.argu_count: %d.\n", problem.argu_count);
    // while (scan < problem.argu_count)
    //   printf("%s ", problem.asp_argument[scan++]);
    // printf("\n");

    // ApproxSMC(ctl, &problem);

    // create a control object and pass command line arguments
    if (!clingo_control_new(problem.asp_argument, problem.argu_count, NULL, NULL, 20, &ctl) != 0) {
        goto error;
    }

    // register propagator object
    clingo_control_register_propagator(ctl, &prop, &prop_data, false);

    // add a logic program to the base part
    // if (!clingo_control_add(ctl, "base", NULL, 0, "{a; b; c}."))
    // {
    //   goto error;
    // }

    clingo_control_load(ctl, problem.asp_file.c_str());
    if (problem.input_file)
        clingo_control_load(ctl, problem.input_file);

    if (debug) {
        std::ifstream fin;
        fin.open(problem.asp_file);
        debug_out.open("debug.txt", std::ios::trunc);
        debug_out << fin.rdbuf() << std::endl;
        if (problem.input_file) {
            fin.open(problem.input_file);
            debug_out << fin.rdbuf() << std::endl;
        }
    }

    // ground the base part
    if (!clingo_control_ground(ctl, parts, 1, NULL, NULL)) {
        goto error;
    }
    get_symbol_atoms(ctl, &problem);
    generate_k_xors(3, &problem);
    translation(&ctl, &problem, debug, debug_out);
    if (!clingo_control_ground(ctl, parts, 1, NULL, NULL)) {
        goto error;
    }
    // clingo_control_add();
    // print_all(&problem);
    // solve

    if (!solve(ctl, &buf, &solve_ret)) {
        goto error;
    }
    add_execution_time(ctl, &problem);
    prop_data.solver->printStatistics();
    // printf("%g", problem.time_in_clasp);
    goto out;

error:
    if (!(error_message = clingo_error_message())) {
        error_message = "error";
    }

    printf("%s\n", error_message);
    ret = clingo_error_code();

out:
    free_model_buffer(&buf);
    if (ctl) {
        clingo_control_free(ctl);
    }

    return ret;
}
