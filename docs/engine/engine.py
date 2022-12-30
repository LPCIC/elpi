#!/usr/bin/env python3

# Available options #########################################################

atext       = ':assert:'   # regexp            - fail if not matched
noerrtext   = ':nostderr:' #                   - omit stderr, by default show
cmdlinetext = ':cmdline:'  # arguments to elpi - override default which is -test

options =               [atext , noerrtext, cmdlinetext ]
initial_option_status = (''    , False,     ['-test']   )

#############################################################################

import os, sys, in_place, pathlib, subprocess, re, shlex

def check(input, expression):
    if expression == '':
        return True
    pattern = re.compile('.*' + expression, re.IGNORECASE | re.MULTILINE | re.DOTALL)
    rc = pattern.match(input)
    return rc

def run(o, path, base_path):
    _, _, cmd = o

    if len(path) > 0:
        file = [(base_path / path).as_posix()]
    else:
        file = []

    exec = ['dune', 'exec', 'elpi', '--'] + file + cmd
    print('  - Executing:',' '.join(exec))
    elpi = subprocess.Popen(exec, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    output, errors = elpi.communicate()
    elpi.wait()
    return output, errors

def parse_option(o, line):
    a,e,c = o
    if line.startswith(atext):
        a = line[len(atext):].strip()
        return (a,e,c)
    elif line.startswith(noerrtext):
        e = True
        return (a,e,c)
    elif line.startswith(cmdlinetext):
        c = shlex.split(line[len(cmdlinetext):].strip())
        return (a,e,c)
    else:
        print ('Error parsing options:',line)
        exit(1)

def process(source, base_path):
    stext = '.. elpi::'
    rtext = '.. literalinclude::'

    file_ = open(source, 'r')
    lines = file_.readlines()

    with in_place.InPlace(source) as file:

        index = 0
        
        for line in file:

            path = ''
            output = ''
            errors = ''
            option_status = initial_option_status

            # ship options, already handled
            if any(line.strip().startswith(x) for x in options):
                #file.write('')
                continue

            elif line.strip().startswith(stext):
                indentation = ' '
                indentation *= line.index(':') - 7

                path = line[line.index(':')+2:].strip()

                stop = False
                while not stop and index < len(lines)-1:
                    next = lines[index+1].strip()
                    if any(next.startswith(x) for x in options):
                        index += 1
                        option_status = parse_option(option_status,next)
                    else:
                        stop = True

                output, errors = run(option_status, path, base_path)
                
                assert_expression, skip_stderr, _ = option_status

                if check(output, assert_expression) is None:
                    print('Failed to match',assert_expression,'on:\n')
                    print(output)
                    print(errors)
                    exit(1)

                if len(path) > 0:
                    block  = ''
                    block += line.replace(stext, rtext)
                    block += indentation + '   :linenos:' + '\n'
                    block += indentation + '   :language: elpi' + '\n'
                    file.write(block)

                if len(output) > 0:
                    block  = indentation + '\n'
                    block += indentation + '.. code-block:: console' + '\n'
                    block += indentation + '\n   '
                    block += indentation + output.replace('\n', '\n'+indentation+'   ')
                    block += indentation + '\n'
                    file.write(block)
                    
                if len(errors) > 0 and not skip_stderr:
                    block  = indentation + '\n'
                    block += indentation + '.. code-block:: console' + '\n'
                    block += indentation + '\n   '
                    block += indentation + errors.replace('\n', '\n'+indentation+'   ')
                    block += indentation + '\n'
                    file.write(block)

            else:
                file.write(line)

            index += 1

def find(path):
    files = sorted(path.glob('**/**/*.rst'))
    return files;


print('Elpi documentation - Engine started.')

base_path = os.path.basename(sys.argv[0])
base_path = pathlib.Path(base_path).parent.parent.resolve()
path = base_path / 'docs' / 'source'

print('- Base path.\n', path.as_posix())

for file in find(path):
    print('- Processing file:', file.as_posix())
    process(file.as_posix(), path)

print('Elpi documentation - Engine finished.\n')
