Running a program
=================

The `elpi` command line utility can run a query against a program.
The standard query is `main` for which one can use the dedicated
command line option `-main`.

.. elpi:: cmdline_example.elpi
   :nostderr:

Custom entry point
++++++++++++++++++

.. elpi:: cmdline_example.elpi
   :cmdline: -exec mypred -- 1 a "hi there"
   :nostderr:
   :nocode:

Interactive use
+++++++++++++++

.. elpi:: cmdline_example.elpi
   :cmdline:
   :nocode:

Typing `guess X.` followed by enter runs the query.

.. elpi:: cmdline_example.elpi
   :stdin: guess X.\ny\n
   :nostderr:
   :cmdline:
   :nocode:

Command line options
====================

.. elpi::
   :cmdline: -h


Tracing options
+++++++++++++++

