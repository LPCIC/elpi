###########
Constraints
###########

:doc:`logic-programming-model` ended on a problem. The STLC type checker,
asked about a term that still has a hole in it, has nothing sensible to do:
because its first argument is an input, no rule head matches a bare variable
and the goal simply fails — and with unification in place of matching it does
worse, inventing an ``app`` (then a ``lam`` inside that, and so on) for the
hole and looping forever. Neither is any use to an elaborator, which works
with exactly such *incomplete* terms — full of holes still to be filled in —
all the time. The fix is to let the checker *suspend* on a hole rather than
guess.


Controlling instantiation
==========================

When a rule's search meets a hole, one of two things should happen instead of
guessing: *suspend* the computation, recording it as a constraint to be
retried later, or *synthesize* a value for the hole through some dedicated
routine — one richer than plain unification, and out of scope for this
chapter. A suspended computation can also carry data along, anything from a
single flag to a whole typing sequent, and the data that several suspended
computations have attached to one hole can later be combined. This chapter
covers suspending and resuming; combining what several constraints know about
the same hole is :doc:`chr`.


Matching, not unifying
=======================

The *input* arguments of a signature (:doc:`../syntax/type-declarations`,
:doc:`../features/modes`) are not unified with the goal when a rule is
selected; they are *matched* against the rule's head instead. A unification
variable that the goal left unassigned in an input position therefore stays
unassigned — trying a rule never fills it in.

That is what lets a rule detect a hole and act on it. The ``uvar`` keyword is
a head pattern that matches only an unassigned variable, and ``uvar as E``
binds ``E`` to it. The two rules below are equivalent — the second spells out
what the first means:

.. code-block:: elpi

   of (uvar as E) T :- declare_constraint (of E T) [E].
   % equivalent to:
   of E T :- var E, declare_constraint (of E T) [E].

:doc:`../features/modes` has the full set of ``uvar`` head patterns, among
them ``uvar Hd Args`` for taking apart a hole that has been *applied* to
arguments.

``declare_constraint`` (:doc:`../syntax/constraint-handling-rules`) is what
turns a goal into a constraint. Its goal argument must itself be a *function*
— it needs a ``func`` signature — because a constraint that could be resumed
in more than one way would make the search unpredictable once constraint
handling rules start combining constraints.


Suspending and resuming
=========================

The STLC checker of :doc:`../examples/stlc` handles an incomplete term with
one extra rule — the ``uvar`` one below — that gives a hole a sensible
meaning in place of the failure or the infinite loop:

.. code-block:: elpi

   func of tm -> ty.
   of (app H A) T :- of H (arr S T), of A S.
   of (lam F) (arr S T) :- pi c\ of c S ==> of (F c) T.
   of (uvar as E) T :- declare_constraint (of E T) [E].

Now ``of (app H A) T`` with ``H`` and ``A`` both unknown succeeds, leaving two
suspended goals that record what is still to be checked once ``H`` and ``A``
become known (the Example below shows the store). When ``H`` is later
assigned, its constraint is resumed like any other suspended goal and
simplifies: the constraint left over now mentions ``H``'s former unknown type
directly, rather than behind an arrow.

The list passed to ``declare_constraint`` is the constraint's *trigger* — the
variables whose assignment wakes it up. A constraint honours backtracking
just as a plain unification assignment does: undoing the assignment that
resumed a constraint suspends it again, as though nothing had happened.

.. elpi:: ../code/backtracking-constraints.elpi
   :assert: before:\n even X\d+  /\* suspended on X\d+ \*/\nafter backtracking:\n even X\d+  /\* suspended on X\d+ \*/


Incompatible constraints
==========================

Suspending and resuming on their own are not quite enough. The goal
``of (app D D) T`` — an unknown ``D`` applied to itself — succeeds, with two
constraints about that one ``D``: one says ``D`` has some type ``S``, the
other that ``D`` has a function type ``S -> T``. Each is a perfectly good
suspended goal on its own; together they are contradictory, and the term
should have been rejected. Nothing covered so far can express "take every
constraint about the same hole together and decide" — that is what
:doc:`chr` adds.

One rule is enough for this case: whenever two ``of`` constraints are about
the same hole, keep the first and unify the second type with it.

.. code-block:: elpi

   constraint of {
     rule (of X S1) \ (of X S2) <=> (S1 = S2).
   }

On ``of (app D D) T`` that rule fires on the two constraints above and runs
``S = arr S T``, which fails the occur check — so the term is now rejected,
as it should be:

.. elpi:: ../code/incompatible.elpi
   :assert: of \(app D D\): rejected

The rule, the ``constraint`` block it lives in, and how such a rule sees the
store are :doc:`../syntax/constraint-handling-rules` and :doc:`chr`.


Example
=======

.. elpi:: ../code/holes.elpi
   :assert: before:\n of X\d+ X\d+  /\* suspended on X\d+ \*/ of X\d+ \(arr X\d+ X\d+\)  /\* suspended on X\d+ \*/\nafter:\n of X\d+ X\d+  /\* suspended on X\d+ \*/
