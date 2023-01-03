#!/usr/bin/env python3

# Available options #########################################################

atext       = ':assert:'   # regexp            - fail if not matched
noerrtext   = ':nostderr:' #                   - omit stderr, by default show
stdintext   = ':stdin:'    #                   - specify stdin
nocodetext  = ':nocode:'   #                   - omit code, by default show
cmdlinetext = ':cmdline:'  # arguments to elpi - override default which is -main

options =               [atext , noerrtext, nocodetext, cmdlinetext, stdintext ]
initial_option_status = (''    , False,     False,      ['-main']  , ''        )

#############################################################################

import os, sys, in_place, pathlib, subprocess, re, shlex, copy

def check(input, expression):
    if expression == '':
        return True
    pattern = re.compile('.*' + expression, re.IGNORECASE | re.MULTILINE | re.DOTALL)
    rc = pattern.match(input)
    return rc

def run(o, path, base_path):
    _, _, _, cmd, s = o

    if len(path) > 0:
        file = [(base_path / path).as_posix()]
    else:
        file = []

    exec = ['dune', 'exec', 'elpi', '--'] + file + cmd
    print('  - Executing:',' '.join(exec),'|',s)
    elpi = subprocess.Popen(exec, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.PIPE, text=True)
    output, errors = elpi.communicate(input=(s+'\n'))
    elpi.wait()
    return output, errors

def parse_option(o, line):
    a,e,x,c,i = o
    if line.startswith(atext):
        a = line[len(atext):].strip()
        return (a,e,x,c,i)
    elif line.startswith(noerrtext):
        e = True
        return (a,e,x,c,i)
    elif line.startswith(nocodetext):
        x = True
        return (a,e,x,c,i)
    elif line.startswith(cmdlinetext):
        c = shlex.split(line[len(cmdlinetext):].strip())
        return (a,e,x,c,i)
    elif line.startswith(stdintext):
        i = line[len(stdintext):].replace('\\n','\n')
        return (a,e,x,c,i)
    else:
        print ('Error parsing options:',line)
        exit(1)

def process(source, base_path):
    stext = '.. elpi::'

    file_ = open(source, 'r')
    lines = file_.readlines()

    with in_place.InPlace(source) as file:

        index = 0

        file.write('.. role:: console(code)\n')
        file.write('   :language: shell\n\n')   
        for line in file:

            path = ''
            output = ''
            errors = ''
            option_status = copy.deepcopy(initial_option_status)

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
                
                assert_expression, skip_stderr, skip_code, command_line, _ = option_status

                if check(output, assert_expression) is None:
                    print('Failed to match',assert_expression,'on:\n')
                    print(output)
                    print(errors)
                    exit(1)

                if len(path) > 0 and not skip_code:
                    block  = ''
                    block += indentation + '.. literalinclude:: ' + path + '\n'
                    block += indentation + '   :caption: ' + path + '\n'
                    block += indentation + '   :linenos:' + '\n'
                    block += indentation + '   :language: elpi' + '\n'
                    file.write(block)

                if len(path) > 0:
                    file.write('\n' + indentation + 'Output of :console:`elpi ' + shlex.join([path] + command_line) + '`\n')
                else:
                    file.write('\n' + indentation + 'Output of :console:`elpi ' + shlex.join(         command_line) + '`\n')

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
