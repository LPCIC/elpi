#########################
Debugging and tracing
#########################

Elpi's interpreter is instrumented. Each traced event is one application of a
rule of :doc:`semantics/formal-semantics`: ``curgoal`` marks the goal now
active, ``rule`` the backchain step that picks a clause for it, ``newgoal``
the premises that step pushes, ``assign`` an extension of the substitution,
``new-hyps`` and ``new-quant`` the ``==>`` and ``pi`` steps. The operational
semantics rewrites a single configuration and keeps no call stack, so the
event stream is flat and linear; a separate *elaborator* rebuilds the goal
tree from the parent/child links in the stream, and that reconstructed tree is
what the interactive browser shows.

Three tools sit at increasing distance from the running program: ``std.spy``
prints from inside it with no flags; the trace facility emits the event
stream, as text or JSON, under command-line control; and the trace browser
displays the elaborated tree.


``std.spy``
=============

``std.spy G`` runs ``G`` and prints it on entry, and again on exit or on
failure, through ``std.debug-print``, so it is subject to the same
overriding as any other library hook (:doc:`standard-library`). ``std.spy!``
is the same with a cut, for a goal that should only ever succeed once.

.. elpi:: code/spy-tour.elpi
   :assert: ----<<---- enter:  double 5 X\d+\n---->>---- exit:  double 5 10\nresult: 10


The tracing facility
=======================

``elpi prog.elpi -test -trace-on -trace-at run 1 9999 -trace-only 'user:'``
prints one line per traced event (a goal selected (``run``), a rule tried
(``select``), a variable assigned (``assign``), and more) between step 1 and
step 9999 of the ``run`` trace point:

.. code-block:: console

   $ elpi prog.elpi -test -trace-on -trace-at run 1 5 -trace-only 'user:'
     rid:0 step:1 gid:4 user:curgoal = main ...
     rid:0 step:1 gid:4 user:rule = backchain
     rid:0 step:1 gid:5 user:newgoal = double 5 X0
     ...

``-trace-only-pred REX`` narrows the trace to goals matching a predicate
name; ``-trace-skip REX`` excludes matching items instead. Events prefixed
``user:`` come from the program; ``dev:`` ones are for debugging Elpi itself.
``trace.counter "NAME" N`` reads a named counter (``"run"`` counts solved
goals) for a program to condition its own debug output on, the way
``std.spy`` does.

``elpi -print-ast FILE`` prints a program as parsed, before any compilation
pass; ``elpi -print FILE`` prints it after most of them, spilling
(:doc:`features/spilling`) included, so any question about how a particular
piece of surface syntax desugared can be checked directly. ``elpi FILE -deps``
prints the ``accumulate`` graph of ``FILE`` and everything it pulls in, as a
Graphviz ``digraph``, useful for untangling a large project's file structure
(:doc:`syntax/file-structure-and-attributes`).


The trace browser
=====================

``elpi prog.elpi -test -trace-on json FILE -trace-at run 1 9999`` writes a
machine-readable trace instead of a text one. ``elpi-trace-elaborator``, a
separate binary shipped with Elpi, reads such a trace from standard input and
groups it into "cards", one per step with its rule and its subgoals, the
shape the VS Code extension's trace browser (:doc:`getting-started`) displays
and steps through interactively, rather than a flat log.
