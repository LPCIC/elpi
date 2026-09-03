###############
Getting started
###############

Installing Elpi
=================

The recommended way to install Elpi is through opam:

.. code-block:: console

   $ opam install elpi

This installs the ``elpi`` command-line tool used throughout this manual and
the ``elpi`` findlib package that an OCaml application links against to embed
the interpreter (``-package elpi``, see :doc:`embedding`).

Elpi is also packaged for Nix and for Debian and its derivatives.

In addition, every continuous-integration run produces statically linked
binaries for Linux, macOS and Windows, downloadable from the `project's
Actions tab <https://github.com/LPCIC/elpi/actions>`_. These carry no
dependencies, so downloading one is often the quickest way to start
experimenting.


Running a program
====================

An Elpi program is a collection of rules kept in one or more ``.elpi`` files.
Here is a complete one. Running it with ``-test`` executes the query ``main``; the
output ``main`` prints is shown below the listing:

.. elpi:: code/hello.elpi
   :assert: Hello, world!

The program declares one predicate, ``greeting``, gives it a single defining
rule that relates it to a string, and defines ``main`` to look that string up
and print it. ``elpi FILE -test`` always runs the query ``main`` this way.

To run a different query, use ``-exec``. The invocation ``elpi hello.elpi
-exec p -- a b c`` runs the query ``p ["a", "b", "c"]``, passing whatever
follows ``--`` on the command line as a single list-of-strings argument.

With neither ``-test`` nor ``-exec``, ``elpi`` prints a ``goal>`` prompt,
reads one goal from standard input, runs it, and exits. This is the quickest
way to try a query against a program without editing it, for instance to
see what ``greeting`` binds its argument to:

.. code-block:: console

   $ elpi hello.elpi
   goal> greeting S.
   Success:
     S = Hello, world!

The prompt reports the answer substitution (here just ``S``), followed by any
leftover constraints and the final state, both empty in this case. Typing
``main.`` at the prompt instead would run ``main``, printing ``Hello, world!``
and succeeding with no bindings. The prompt handles one goal per run; to try
several queries, start ``elpi`` again for each, or drive the interpreter
through its OCaml API (:doc:`embedding`).

A few command-line flags matter from the first program on:

* ``-I PATH`` adds a directory to the search path used to resolve
  ``accumulate`` directives (:doc:`syntax/file-structure-and-attributes`); it
  may be passed more than once;
* ``--help`` lists every flag;
* ``--version`` prints the Elpi version


Editor support
================

An `extension for Visual Studio Code <https://github.com/LPCIC/elpi-lang>`_ is
available in the marketplace; search for "Elpi". Besides syntax highlighting,
it hosts the interactive trace browser described in
:doc:`debugging-and-tracing`.
