###########################
Input and output arguments
###########################

A ``pred`` / ``func`` signature (:doc:`../syntax/type-declarations`) splits
arguments into **input** (before ``->``) and **output** (after it — a pure
relation has none: ``pred name -> Out..``). This chapter is what that split
means when a rule is tried; :doc:`../semantics/constraints` covers why it
exists at all.


Matched, not assigned
=======================

Selecting a rule *matches* the goal's input arguments against the rule head's
patterns, and *unifies* its output arguments with them
(:doc:`../semantics/formal-semantics`'s ``select``). The difference shows as
soon as one argument is an unassigned variable: matching it against a
constant pattern would have to assign it, so it simply fails to match instead
— no rule fires, and the variable is untouched. Unifying it, on the other
hand, succeeds and assigns it:

.. elpi:: ../code/input-output.elpi
   :assert: as-input X: no rule matched an unassigned X\nas-output assigned Y to z

This is what makes input arguments safe to leave partially unknown: a call
with a hole in an input position does not force a guess, it just finds no
matching rule (or suspends, if the predicate has an ``uvar`` rule of its own —
:doc:`../syntax/constraint-handling-rules`).


Matching an open input on purpose
====================================

To write a rule that *does* fire on an unassigned input, match it with
``uvar`` (:doc:`../syntax/inference-rules-and-queries`); ``uvar as N`` also
names it, for the rest of the rule to use:

.. code-block:: elpi

   even (uvar as X) :- !, declare_constraint (even X) [X].

The standalone ``mode`` directive — the older, separate way of marking
arguments input/output — is :doc:`../compatibility`.
