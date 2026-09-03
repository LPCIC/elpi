###############
Control and cut
###############

``!`` is a hard cut: it discards not only a predicate's untried rules but the
choice points of premises already solved in the same rule
(:doc:`../semantics/logic-programming-model`,
:doc:`../semantics/formal-semantics`). The rest are the control constructs
built on it.


Cut and disjunction
=====================

``!`` discards every choice point created since the *rule* it appears in was
selected, including one opened by a ``;`` earlier in the same body, not only
the rule's own untried alternatives:

.. code-block:: elpi

   describe N R :- 0 is N mod 2, !, R = "even".
   describe _ "odd".

Once the first rule's guard succeeds, ``!`` commits: on backtracking, Elpi
does not try to make ``R`` something other than ``"even"``, and does not fall
through to the second rule either. Both were choices made after the cut's
rule was entered.


``not``, ``if`` and ``if2``
=============================

``not G`` succeeds iff ``G`` has no solution. It is defined as
``not X :- X, !, fail. not _.``, so it commits to the first solution of ``G``,
if any, before failing. ``if C T E`` commits to the first solution of ``C``,
if any, and runs ``T``; otherwise it runs ``E``. It is a packaged cut,
cheaper to read than ``(C, !, T ; E)``. ``if2`` is the same with two
conditions tried in order, and a final ``else``:

.. code-block:: elpi

   func if  (pred), (func), (func).
   func if2 (pred), (func), (pred), (func), (func).


``halt`` and ``stop``
=======================

``halt`` (variadic: it accepts anything ``print``-able) stops the whole
process immediately, printing its arguments first, for a fatal error.
``stop`` fails the current goal without terminating the process, so outer
alternatives are still tried.


Taming backtracking
======================

``std.once G`` is ``G`` with an implicit cut right after its first success,
for a relation that naturally has several solutions when only the first is
wanted. ``std.do! [G1, G2, …]`` runs a sequence of goals each followed by a
cut, so a failure never triggers backtracking into an earlier one, closer to
imperative sequencing than a plain conjunction.

Each of these in one program, a cut committing a disjunction, then ``not``,
``if``, ``std.once`` and ``std.do!``:

.. elpi:: ../code/control.elpi
   :assert: 4 is even\n3 is odd\nnot \(even 3\) succeeds\nif: 4 is even\nonce picked the first match: 3\ndo!: step 1\ndo!: step 2
