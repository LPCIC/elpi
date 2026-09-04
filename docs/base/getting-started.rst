###############
Getting started
###############

Installing Elpi
=================

.. code-block:: console

   $ opam install elpi

installs the ``elpi`` command-line tool and the ``elpi`` findlib package
(``-package elpi``, for :doc:`embedding`). To track the development version,
``opam pin add elpi https://github.com/LPCIC/elpi.git``, or clone the
repository and run ``make build``. Every CI run also produces statically
linked binaries for Linux, macOS and Windows, downloadable from the
project's Actions tab.


Running a program
====================

.. code-block:: console

   $ elpi hello.elpi -test

parses ``hello.elpi``, and every other file it ``accumulate``s
(:doc:`syntax/file-structure-and-attributes`), type-checks and determinacy-checks
the result, and runs the query ``main``. ``elpi hello.elpi -exec p -- a b c``
runs ``p ["a", "b", "c"]`` instead; with no ``-test``/``-exec`` and a goal
piped or typed on standard input, ``elpi`` opens an interactive ``goal>``
prompt. All three are :doc:`syntax/inference-rules-and-queries`.

A few flags matter from the first program on: ``-D NAME`` defines a compiler
variable, for ``:if`` (:doc:`features/conditional-compilation`); ``-I PATH``
adds a directory to the search path used to resolve ``accumulate``
(:doc:`features/program-organization`); ``--version`` and ``--help`` are the
usual. ``elpi --help`` lists every flag, including the tracing ones
(:doc:`debugging-and-tracing`).


Editor support
================

An `extension for Visual Studio Code <https://github.com/LPCIC/elpi-lang>`_ is
available in the marketplace (search for "Elpi"). For Vim, the project's
``README.md`` ships a ``.vimrc`` snippet that gives ``.elpi`` files λProlog
syntax highlighting plus Elpi's own keywords, macros and spilling braces.
