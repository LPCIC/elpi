#########################
Debugging and tracing
#########################

``std.spy``
=============

``std.spy G`` runs ``G`` and prints it on entry, and again on exit or on
failure — through ``std.debug-print``, so it is subject to the same
overriding as any other library hook (:doc:`standard-library`). ``std.spy!``
is the same with a cut, for a goal that should only ever succeed once.

.. elpi:: code/spy-tour.elpi
   :assert: ----<<---- enter:  double 5 X\d+\n---->>---- exit:  double 5 10\nresult: 10


The tracing facility
=======================

``elpi prog.elpi -test -trace-on -trace-at run 1 9999 -trace-only 'user:'``
prints one line per traced event — a goal selected (``run``), a rule tried
(``select``), a variable assigned (``assign``), and more — between step 1 and
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
``trace.counter "NAME" N`` reads a named counter — ``"run"`` counts solved
goals — for a program to condition its own debug output on, the way
``std.spy`` does.

``elpi -print-ast FILE`` prints a program exactly as parsed, before any
compilation pass; ``elpi -print FILE`` prints it after most of them —
including spilling (:doc:`features/spilling`) — so any question about how a
particular piece of surface syntax desugared can be checked directly.


The trace browser
=====================

``elpi prog.elpi -test -trace-on json FILE -trace-at run 1 9999`` writes a
machine-readable trace instead of a text one. ``elpi-trace-elaborator``, a
separate binary shipped with Elpi, reads such a trace from standard input and
groups it into "cards" — one per step, its rule and its subgoals — the shape
the VS Code extension's trace browser (:doc:`getting-started`) displays and
lets you step through interactively, rather than reading a flat log.
