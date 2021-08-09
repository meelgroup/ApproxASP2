import os, argparse, subprocess

tool_dir = "tools"
parser = argparse.ArgumentParser()
parser.add_argument('-i','--i', help='Description', required=True)
args = parser.parse_args()

file_name = args.i

os.system('gringo -o smodels {1} > grounded_{1}'.format(tool_dir, file_name))
program_atoms = dict()

grounded_file = open('grounded_{0}'.format(file_name), 'r')
atom_section_started = False

for line in grounded_file:
    if line.startswith("0") and not atom_section_started:
        atom_section_started = True
    elif line.startswith("0") and atom_section_started:
        break
    elif atom_section_started:
        l = line.split()
        program_atoms[int(l[0])] = l[1]

grounded_file.close()
initial_ind_sup_str = "c ind "
for lit in program_atoms.keys():
    initial_ind_sup_str += str(lit) + " "
initial_ind_sup_str += "0"

os.system('{0}/lp2normal-2.27 grounded_{1}| {0}/lp2lp2-1.23 -l | {0}/lp2sat-1.24 > cnf_{1}'.format(tool_dir, file_name))

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

independent_support_string = "".join(_ + " " for _ in l)
os.system('echo "{0}" > IS_{1}'.format(independent_support_string, file_name))
os.system('rm cnf_{0} grounded_{0}'.format(file_name))



