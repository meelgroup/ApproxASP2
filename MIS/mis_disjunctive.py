import os, argparse, subprocess

tool_dir = "tools"
parser = argparse.ArgumentParser()
parser.add_argument('-i','--i', help='Description', required=True)
args = parser.parse_args()

file_name = args.i

os.system('gringo -o smodels {1} | {0}/lp2normal-2.27 > normalized_{1}'.format(tool_dir, file_name))
program_atoms = dict()

norm_file = open('normalized_{0}'.format(file_name), 'r')
new_norm_file = open('new_normalized_{0}'.format(file_name), 'w')

incomplete_literal = []
new_definitions = []
literal = subprocess.Popen('tools/len-1.13 -a normalized_{0}'.format(file_name), shell=True, stdout=subprocess.PIPE).stdout
max_literal = literal.read().decode("utf-8").strip()
max_literal_index = int(max_literal) + 1
atom_section_started = False
atom_section_end = False
for line in norm_file:
    modified_line = line
    if line.startswith("0") and not atom_section_started and not atom_section_end:
        atom_section_started = True
    elif line.startswith("0") and atom_section_started:
        # adding comments for disjunctive heads
        for _ in range(max_literal_index, max_literal_index + len(new_definitions)):
            comment_line = "{0} head_of_disjunctive({1})\n".format(_, _ - max_literal_index + 1)
            new_norm_file.write(comment_line)

        atom_section_started = False
        atom_section_end = True
    elif atom_section_started:
        l = line.split()
        program_atoms[int(l[0])] = l[1]
    if line.startswith("8 "):
        l = line.split()
        new_atom_index = len(new_definitions) + max_literal_index
        or_head = [new_atom_index]
        number_of_head_atoms = int(l[1])
        for _ in range(number_of_head_atoms):
            incomplete_literal.append(int(l[2 + _]))
            or_head.append(int(l[2 + _]))

        new_definitions.append(or_head)

        l = l[number_of_head_atoms:]
        l[0] = '1'
        l[1] = str(new_atom_index)
        modified_line = "".join(_ + " " for _ in l)
        modified_line += "\n"

    new_norm_file.write(modified_line)


norm_file.close()
new_norm_file.close()

if len(new_definitions) > 0:
    os.system('mv new_normalized_{0} normalized_{0}'.format(file_name))

initial_ind_sup_str = "c ind "
for lit in program_atoms.keys():
    initial_ind_sup_str += str(lit) + " "
initial_ind_sup_str += "0"

os.system('{0}/lp2sat-1.24 normalized_{1} > cnf_{1}'.format(tool_dir, file_name))

# treatment for disjunctive logic programs
cnf_file = open('cnf_{0}'.format(file_name), 'r')
new_cnf_file = open('new_cnf_{0}'.format(file_name), 'w')
for line in cnf_file:
    modified_line = line
    l = line.split()
    if len(l) == 2 and -int(l[0]) in incomplete_literal:
        continue

    new_cnf_file.write(modified_line)

for a in new_definitions:
    clause1 = str(-a[0])
    for _ in range(1, len(a)):
        clause2 = str(-a[_]) + " " + str(a[0]) + " 0\n"
        new_cnf_file.write(clause2)
        clause1 += (" " + str(a[_]))
    new_cnf_file.write(clause1 + " 0\n")

cnf_file.close()
new_cnf_file.close()

if len(new_definitions) > 0:
    os.system('mv new_cnf_{0} cnf_{0}'.format(file_name))

first_line = subprocess.Popen('head -n 1 cnf_{0}'.format(file_name), shell=True, stdout=subprocess.PIPE).stdout
stat = first_line.read().decode("utf-8").strip().split()
new_clause = subprocess.Popen('grep "^[^p|^c]" cnf_{0} | wc -l'.format(file_name), shell=True, stdout=subprocess.PIPE).stdout
stat[3] = new_clause.read().decode("utf-8").strip()
first_line = " ".join(stat)

os.system('sed -i \'1s/.*/%s/\' %s'%(first_line, 'cnf_{0}'.format(file_name)))
os.system('sed -i \'1 i\%s\' %s'%(initial_ind_sup_str, 'cnf_{0}'.format(file_name)))
independent_support = subprocess.Popen('{0}/arjun %s | grep "vp"'.format(tool_dir) %('cnf_{0}'.format(file_name)), shell=True, stdout=subprocess.PIPE).stdout
independent_support_string =  independent_support.read().decode("utf-8").strip().replace("vp", "c ind")

l = independent_support_string.split()
print('Initial independent support size: {0}'.format(len(program_atoms.keys())))
print('Final independent support size: {0}'.format(len(l) - 3))

for index, item in enumerate(l):
    if index <= 1 or index == len(l) - 1:
        continue
    l[index] = program_atoms[int(item)]

independent_support_string = ""
for index, item in enumerate(l):
    if index < len(l) - 1:
        independent_support_string += (item + " ")
    else:
        independent_support_string += item

os.system('echo "{0}" > IS_{1}'.format(independent_support_string, file_name))
os.system('rm normalized_{0}'.format(file_name))