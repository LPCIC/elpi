#!/usr/bin/env python3

import os, sys, in_place, pathlib, subprocess

def exec(path, base_path):
    file = base_path / path
    print('  - Executing elpi on', file.as_posix())
    elpi = subprocess.Popen(['dune', 'exec', 'elpi', '--', '-test', file.as_posix()[:-1]], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    output, errors = elpi.communicate()
    elpi.wait()
    return output, errors

def process(source, base_path):
    stext = '.. elpi::'
    rtext = '.. literalinclude::'

    with in_place.InPlace(source) as file:
        for line in file:

            output = ''
            errors = ''

            if line.startswith(stext):
                path = line[10:]
                output, errors = exec(path, base_path)
                # print('  - STDOUT:')
                # print(output)
                # print('  - STDERR:')
                # print(errors)

            line = line.replace(stext, rtext)

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
