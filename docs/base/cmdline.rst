Running a program
=================

The :console:`elpi` command line utility can run a query against a program.
The standard query is :elpi:`main` for which one can use the dedicated
command line option :console:`-main`.

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

.. elpi:: cmdline_interactive.elpi
   :cmdline:

Typing :elpi:`guess X.` followed by enter runs the query.

.. elpi:: cmdline_interactive.elpi
   :stdin: guess X.\ny\n
   :nostderr:
   :cmdline:
   :nocode:

Command line options
====================

.. elpi::
   :cmdline: -h

Debug parsing
+++++++++++++

.. elpi::
   :stdin: a ++-> b **? c
   :cmdline: -parse-term
   :nocode:

Tracing options
+++++++++++++++

