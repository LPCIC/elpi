###############
Control and cut
###############

:doc:`../semantics/logic-programming-model` and
:doc:`../semantics/formal-semantics` describe *why* ``!`` is a hard cut. This
chapter is the concrete toolbox built on it.


Cut and disjunction
=====================

``!`` discards every choice point created since the *rule* it appears in was
selected — including one opened by a ``;`` earlier in the same body, not just
the rule's own untried alternatives:

.. code-block:: elpi

   describe N R :- 0 is N mod 2, !, R = "even".
   describe _ "odd".

Once the first rule's guard succeeds, ``!`` commits: on backtracking, Elpi
does not try to make ``R`` something other than ``"even"``, and does not fall
through to the second rule either — both were choices made after the cut's
rule was entered.


``not``, ``if`` and ``if2``
=============================

``not G`` succeeds iff ``G`` has no solution — it is defined as
``not X :- X, !, fail. not _.``, so it commits to the first solution of ``G``,
if any, before failing. ``if C T E`` commits to the first
solution of ``C``, if any, and runs ``T``; otherwise it runs ``E`` — a cut
wrapped for you, cheaper to read than ``(C, !, T ; E)``. ``if2`` is the same
with two conditions tried in order, and a final ``else``:

.. code-block:: elpi

   func if  (pred), (func), (func).
   func if2 (pred), (func), (pred), (func), (func).


``halt`` and ``stop``
=======================

``halt`` (variadic: it accepts anything ``print``-able) stops the whole
process immediately, printing its arguments first — for a fatal error.
``stop`` just fails the current goal without terminating the process, so
outer alternatives are still tried.


Taming backtracking
======================

``std.once G`` is ``G`` with an implicit cut right after its first success
— handy on a relation that naturally has several solutions, when only the
first is wanted. ``std.do! [G1, G2, …]`` runs a sequence of goals each
followed by a cut, so a failure never triggers backtracking into an earlier
one — closer to imperative sequencing than a plain conjunction.


Example
=======

.. elpi:: ../code/control.elpi
   :assert: 4 is even\n3 is odd\nnot \(even 3\) succeeds\nif: 4 is even\nonce picked the first match: 3\ndo!: step 1\ndo!: step 2
