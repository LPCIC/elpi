###########
Constraints
###########

The previous chapter, :doc:`logic-programming-model`, ended on a problem. The
STLC type checker, asked about a term that still has a hole in it, has nothing
sensible to do:
because its first argument is an input, no rule head matches a bare variable
and the goal simply fails. With unification in place of matching it does
worse, inventing an ``app`` (then a ``lam`` inside that, and so on) for the
hole and looping forever. Neither is any use to an elaborator, which works
with such *incomplete* terms, full of holes still to be filled in, all the
time. The fix is to let the checker *suspend* on a hole rather than guess.


Controlling instantiation
==========================

When a rule's search meets a hole, one of two things should happen instead of
guessing: *suspend* the computation, recording it as a constraint to be
retried later, or *synthesize* a value for the hole through some dedicated
routine richer than plain unification (out of scope for this chapter). A
suspended computation can also carry data along, anything from a single flag
to a whole typing sequent, and the data that several suspended computations
have attached to one hole can later be combined. Suspending and resuming are
what follow; combining what several constraints know about the same hole is
covered in :doc:`chr`.


Matching, not unifying
=======================

A signature (:doc:`../syntax/type-declarations`) splits a predicate's
arguments into *input*, before the ``->``, and *output*, after it. When a
rule is selected the two are treated differently: the goal's input arguments
are *matched* against the rule head's patterns, its output arguments are
*unified* with them (:doc:`formal-semantics`'s ``select``). The difference
shows as soon as an argument is an unassigned variable. Matching it against a
constant pattern would have to assign it, so it simply fails to match, no rule
fires, and the variable is left untouched. Unifying it succeeds and assigns
it:

.. elpi:: ../code/input-output.elpi
   :assert: as-input: an unassigned variable matched no rule\nas-output assigned Y to z

An input argument is therefore safe to leave partly unknown: a call with a
hole in an input position does not force a guess, it finds no matching rule.
And that is what lets a rule detect a hole and act on it. The ``uvar``
keyword is a head pattern that matches only an unassigned variable, and
``uvar as E`` binds ``E`` to it. The two rules below are equivalent, the
second spelling out what the first means:

.. code-block:: elpi

   of (uvar as E) T :- declare_constraint (of E T) [E].
   % equivalent to:
   of E T :- var E, declare_constraint (of E T) [E].

The full set of ``uvar`` head patterns is in
:doc:`../features/unification-and-variables`. The standalone ``mode``
directive, the older and separate way of
marking arguments input or output, is described in :doc:`../compatibility`.

``declare_constraint`` (:doc:`../syntax/constraint-handling-rules`) is what
turns a goal into a constraint. Its goal argument must itself be a *function*,
needing a ``func`` signature, because a constraint that could be resumed in
more than one way would make the search unpredictable once constraint handling
rules start combining constraints.


Suspending and resuming
=========================

The list passed to ``declare_constraint`` is the constraint's *trigger*: the
variables whose assignment wakes it up. A constraint honours backtracking
just as a plain unification assignment does: undoing the assignment that
resumed a constraint suspends it again, as though nothing had happened.

.. elpi:: ../code/backtracking-constraints.elpi
   :assert: before:\n even X\d+  /\* suspended on X\d+ \*/\nafter backtracking:\n even X\d+  /\* suspended on X\d+ \*/

The STLC checker from :doc:`logic-programming-model`, with one rule added,
closes the problem that chapter ended on: a hole in argument position now
suspends instead of looping, and resumes when the hole is filled.

.. elpi:: ../code/holes.elpi
   :assert: before:\n of X\d+ X\d+  /\* suspended on X\d+ \*/ of X\d+ \(arr X\d+ X\d+\)  /\* suspended on X\d+ \*/\nafter:\n of X\d+ X\d+  /\* suspended on X\d+ \*/


Incompatible constraints
==========================

Suspending and resuming on their own are not quite enough. Asked about an
unknown ``N``, both ``even N`` and ``odd N`` suspend without complaint. Yet
no number is both, so a goal that suspended the two of them should have
failed. Nothing seen so far looks at a *pair* of constraints and rules them
incompatible; that is what :doc:`chr` adds. A single constraint handling rule
does it here, ``rule (even X) (odd X) <=> false`` in a ``constraint even odd``
block (:doc:`../syntax/constraint-handling-rules`), and ``even N, odd N`` then
fails as soon as the second constraint enters the store:

.. elpi:: ../code/incompatible.elpi
   :assert: even N and odd N: rejected, no number is both
