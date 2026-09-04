###########
Constraints
###########

:doc:`logic-programming-model` ended on a problem: run over a term with an
unconstrained hole, the STLC type checker's own rules make it loop forever,
because unification is happy to invent an ``app`` (or a ``lam``) out of thin
air for an unassigned variable and try again. Elpi is meant to run on
*incomplete* terms — the kind an interactive prover's elaborator manipulates,
full of holes still to be filled in — so this has to be solved.


Controlling instantiation
==========================

When a rule's search meets a hole, one of two things should happen instead of
guessing: **suspend** the computation and record it as a constraint, or
**synthesize** a value for the hole through some dedicated routine (richer
than plain unification, and out of scope for this chapter). Elpi also lets a
suspended computation carry data along — anything from one flag to a whole
typing sequent — and later combine the data attached to the same hole by
several suspended computations. This chapter covers the first two: how to
suspend and resume; combining what several constraints know about the same
hole is :doc:`chr`.


Matching, not unifying
=======================

The **input** arguments of a signature (:doc:`../syntax/type-declarations`,
:doc:`../features/modes`) are not unified with the goal when a rule is
selected: they are *matched* against the rule's head instead. This means no
unification variable occurring in an input argument of the goal is ever
assigned just because a rule was tried.

Matching is spelled out with the ``uvar`` keyword, which stands for a hole in
the head of a rule. ``uvar as E`` binds ``E`` to that hole, and is equivalent
to matching any term and then checking it is unassigned:

.. code-block:: elpi

   of (uvar as E) T :- declare_constraint (of E T) [E].
   % equivalent to:
   of E T :- var E, declare_constraint (of E T) [E].

``declare_constraint`` (:doc:`../syntax/constraint-handling-rules`) is how a
goal is turned into a constraint; its own goal argument must itself be a
**function** — a ``func`` signature — since a constraint that could produce
several different resumptions would make the search behave unpredictably once
combined with constraint handling rules.


Suspending and resuming
=========================

Adding an ``uvar`` rule to the STLC checker gives incomplete terms a sensible
meaning instead of an infinite loop:

.. code-block:: elpi

   func of tm -> ty.
   of (app H A) T :- of H (arr S T), of A S.
   of (lam F) (arr S T) :- pi c\ of c S => of (F c) T.
   of (uvar as E) T :- declare_constraint (of E T) [E].

Now ``of (app H A) T``, with ``H`` and ``A`` both unknown, succeeds — with two
suspended goals recording what remains to be checked once ``H`` and ``A`` are
known (see the Example below). When ``H`` is later assigned, its constraint is
resumed like any other suspended goal, and simplifies: the constraint left
over now mentions ``H``'s former unknown type directly, instead of behind an
arrow.

The list passed to ``declare_constraint`` is the constraint's **trigger**: the
variables whose assignment wakes it up. A constraint honours backtracking
exactly like a plain unification assignment does — undoing an assignment
un-suspends the constraint it had resumed, as if nothing had happened:

.. elpi:: ../code/backtracking-constraints.elpi
   :assert: before:\n even X\d+  /\* suspended on X\d+ \*/\nafter backtracking:\n even X\d+  /\* suspended on X\d+ \*/


Incompatible constraints
==========================

Suspending and resuming alone is not quite enough. The goal ``of (app D D) T``
— applying an unknown ``D`` to itself — succeeds with two constraints about
the very same ``D``: one says ``D`` has some type ``S``, the other that ``D``
has a function type ``S -> T``. Individually each is a perfectly fine
suspended goal; together they are contradictory, so the type checker should
have rejected the term outright. Nothing seen so far can express "look at
every constraint about the same hole together and decide" — that is exactly
what :doc:`chr` adds.


Example
=======

.. elpi:: ../code/holes.elpi
   :assert: before:\n of X\d+ X\d+  /\* suspended on X\d+ \*/ of X\d+ \(arr X\d+ X\d+\)  /\* suspended on X\d+ \*/\nafter:\n of X\d+ X\d+  /\* suspended on X\d+ \*/
