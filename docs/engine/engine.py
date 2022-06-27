#!/usr/bin/env python3

import os, sys, in_place, pathlib, subprocess, re

def check(input, expression):
    pattern = re.compile(expression, re.IGNORECASE)
    return pattern.match(input)

def exec(path, base_path):
    file = base_path / path
    print('  - Executing elpi on', file.as_posix().rstrip())
    elpi = subprocess.Popen(['dune', 'exec', 'elpi', '--', '-test', file.as_posix()[:-1]], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    output, errors = elpi.communicate()
    elpi.wait()
    return output, errors

def process(source, base_path):
    atext = '   :assert:'
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
            matchr = ''

            if line.startswith(atext):
                index += 1
                #file.write('')
                continue

            if line.startswith(stext):
                path = line[10:]

                output, errors = exec(path, base_path)
                
                if index < len(lines)-1:
                    next = lines[index+1]
                    
                    if next.startswith(atext):
                        
                        expression = next[12:].rstrip()
                        
                        if check(output, expression) is None:
                            output = ''
                            errors = ''
                            matchr = 'Injection failure: result did not pass regexp check (' + expression + ')'

            if line.startswith(stext):
                block = '**' + path + ':' + '**' + '\n' + '\n'
                block += line.replace(stext, rtext)
                block += '   :linenos:' + '\n'
                block += '   :language: elpi' + '\n'
                file.write(block)
            else:
                file.write(line)

            if len(output) > 0:
                block  = '\n'
                block += '.. code-block:: console' + '\n'
                block += '\n   '
                block += output.replace('\n', '\n   ')
                block += '\n'
                file.write(block)
                
            if len(errors) > 0:
                block  = '\n'
                block += '.. code-block:: console' + '\n'
                block += '\n   '
                block += errors.replace('\n', '\n   ')
                block += '\n'
                file.write(block)

            if len(matchr) > 0:
                block  = '\n'
                block += '.. raw:: html' + '\n'
                block += '\n   '
                block += '<div class="highlight-console notranslate"><div class="highlight" style="background-color: rgb(248, 148, 148);"><pre>'
                block += matchr
                block += '</pre></div></div>'
                block += '\n'
                file.write(block)
            
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
