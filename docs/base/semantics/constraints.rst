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

:doc:`../features/unification-and-variables` has the full set of ``uvar``
head patterns, among them ``uvar Hd Args`` for taking apart a hole that has
been *applied* to arguments.

``declare_constraint`` (:doc:`../syntax/constraint-handling-rules`) is what
turns a goal into a constraint. Its goal argument must itself be a *function*
— it needs a ``func`` signature — because a constraint that could be resumed
in more than one way would make the search unpredictable once constraint
handling rules start combining constraints.


Suspending and resuming
=========================

The list passed to ``declare_constraint`` is the constraint's *trigger* — the
variables whose assignment wakes it up. A constraint honours backtracking
just as a plain unification assignment does: undoing the assignment that
resumed a constraint suspends it again, as though nothing had happened.

.. elpi:: ../code/backtracking-constraints.elpi
   :assert: before:\n even X\d+  /\* suspended on X\d+ \*/\nafter backtracking:\n even X\d+  /\* suspended on X\d+ \*/


Incompatible constraints
==========================

Suspending and resuming on their own are not quite enough. Asked about an
unknown ``N``, both ``even N`` and ``odd N`` suspend without complaint — yet
no number is both, so a goal that suspended the two of them should have
failed. Nothing seen so far looks at a pair of constraints together and
decides they cannot coexist; that is what :doc:`chr` adds.

One rule is enough here: whenever the store holds ``even N`` and ``odd N``
for the same ``N``, run the goal ``false``.

.. code-block:: elpi

   constraint even odd {
     rule (even X) (odd X) <=> false.
   }

With that rule in the program, ``even N, odd N`` fails as soon as the second
constraint enters the store:

.. elpi:: ../code/incompatible.elpi
   :assert: even N and odd N: rejected, no number is both

The ``rule`` shape, the ``constraint`` block it lives in, and how a rule
matches the store rather than unifying with it are
:doc:`../syntax/constraint-handling-rules` and :doc:`chr`.


Example
=======

.. elpi:: ../code/holes.elpi
   :assert: before:\n of X\d+ X\d+  /\* suspended on X\d+ \*/ of X\d+ \(arr X\d+ X\d+\)  /\* suspended on X\d+ \*/\nafter:\n of X\d+ X\d+  /\* suspended on X\d+ \*/
