#########################
Unification and variables
#########################

A unification variable stands for a term not yet known; it is assigned at
most once, and backtracking undoes the assignment (:doc:`../semantics/logic-programming-model`,
:doc:`../semantics/constraints`). This chapter covers the flags and builtins
around that mechanism: the pattern fragment, the occur check, and the
wildcard.


The pattern fragment
=====================

Elpi's unification is decidable and well-behaved as long as it stays within
the *pattern fragment* (Lλ, Miller's higher-order patterns —
:ref:`Miller, 1992 <bib-miller92>`): a unification variable applied only to
*distinct* bound names. Outside of it, unification can have several — or
infinitely many — most general solutions, and Elpi either picks one
heuristically or delays the problem as a constraint.

Two builtins expose this. ``var V Hd Args`` decomposes an applied unification
variable into its identity ``Hd`` and its argument list ``Args`` (with no
extra arguments, ``var V`` just checks ``V`` is unassigned).
``distinct_names L`` checks that ``L`` is a list of pairwise-distinct bound
names — so, given ``Args`` from ``var``, whether a variable is currently in
the pattern fragment:

.. code-block:: elpi

   pred in-pattern-fragment any.
   in-pattern-fragment X :- var X _ Args, distinct_names Args, !.
   in-pattern-fragment _ :- print "outside the pattern fragment".

A variable's own arguments — the names in scope when it was created via
``pi``/``sigma`` — are always distinct, so a *freshly allocated* variable is
always in the fragment; it is only *later* applications, unification, or
explicit reuse across scopes that can push a term outside it.


The occur check
=================

Unification performs the *occur check* by default: assigning a variable to a
term that already contains it is rejected, rather than building a cyclic
term. Most Prolog systems default the other way, and Elpi's choice is one of
the deliberate departures collected in :doc:`../compatibility`.

``ground_term T`` checks that ``T`` holds no unification variables at all —
useful for asserting that a computation has fully finished, for instance
before serializing a term.

The occur check can be turned off for one predicate with the ``:nooc``
signature attribute. The standard library's ``unsound_unif`` is plain
unification with the check removed, and is defined with ``:nooc`` and
nothing else:

.. literalinclude:: ../../../src/builtin.elpi
   :language: elpi
   :start-at: % Unification without occur check
   :end-at: unsound_unif X X.

So ``X = f X`` fails the occur check, but ``unsound_unif Y (f Y)`` succeeds,
tying ``Y`` into a cyclic term:

.. elpi:: ../code/nooc.elpi
   :assert: = rejects X = f X \(occur check\)\nunsound_unif Y \(f Y\) succeeds

Code that uses ``:nooc`` then has to keep from ever building such a term:
``ground_term`` does not terminate on a cyclic term, and neither do most
other term traversals.


The wildcard ``_``
====================

``_`` is a true wildcard, not a variable: every occurrence is independent, so
two ``_`` in the same head are never forced to be equal, unlike a repeated
named variable — see the Example below.


Example
=======

.. elpi:: ../code/wildcard.elpi
   :assert: same 1 2 fails, as expected\nany 1 2 succeeds, as expected
