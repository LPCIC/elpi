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
    # Like `.. elpi::`: still executed and still checked against a following
    # `:assert:`, but leaves no trace in the rendered manual -- not the
    # directive line itself, not a source listing, not its console output.
    # For a program that must stay verified by the doc build without being
    # reader-facing content (e.g. a test/validation file, as opposed to a
    # worked example).
    htext = '.. elpi-hidden::'
    rtext = '.. literalinclude::'

    file_ = open(source, 'r')
    lines = file_.readlines()

    with in_place.InPlace(source) as file:

        index = 0

        for line in file:

            path = ''

            output = ''
            errors = ''

            if line.startswith(atext):
                index += 1
                #file.write('')
                continue

            hidden = line.startswith(htext)

            if hidden or line.startswith(stext):
                path = line[len(htext)+1:] if hidden else line[len(stext)+1:]

                # Resolve the program path relative to the directory of the
                # .rst file being processed, i.e. the same way Sphinx resolves
                # the `.. literalinclude::` we emit just below. (base_path is
                # the source root, which only coincides with the .rst dir for
                # files sitting at the top of docs/source.)
                output, errors = exec(path, pathlib.Path(source).parent)

                if index < len(lines)-1:
                    next = lines[index+1]

                    if next.startswith(atext):

                        expression = next[12:].rstrip()

                        if check(output, expression) is None:
                            print('Injection failure: ' + path.strip() +
                                  ' did not pass the :assert: check (' + expression + ')',
                                  file=sys.stderr)
                            print('  output was: ' + repr(output), file=sys.stderr)
                            sys.exit(1)

            if hidden:
                # Run and checked above like any other `.. elpi::`; nothing
                # written out below is what keeps it out of the manual.
                pass
            elif line.startswith(stext):
                block = '**' + path.strip() + ':' + '**' + '\n' + '\n'
                block += line.replace(stext, rtext)
                block += '   :linenos:' + '\n'
                block += '   :language: elpi' + '\n'
                file.write(block)
            else:
                file.write(line)

            if not hidden and len(output) > 0:
                block  = '\n'
                block += '.. code-block:: console' + '\n'
                block += '\n   '
                block += output.replace('\n', '\n   ')
                block += '\n'
                file.write(block)

            # `elpi -test` always prints timing/"Success" boilerplate on stderr;
            # only surface it when it carries a real diagnostic.
            if not hidden and len(errors) > 0 and re.search(r'(?i)(error|warning|\bfailure\b)', errors):
                block  = '\n'
                block += '.. code-block:: console' + '\n'
                block += '\n   '
                block += errors.replace('\n', '\n   ')
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
