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
the **pattern fragment** (Lλ, Miller's higher-order patterns —
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

   pred in-pattern-fragment i:any.
   in-pattern-fragment X :- var X _ Args, distinct_names Args, !.
   in-pattern-fragment _ :- print "outside the pattern fragment".

A variable's own arguments — the names in scope when it was created via
``pi``/``sigma`` — are always distinct, so a *freshly allocated* variable is
always in the fragment; it is only *later* applications, unification, or
explicit reuse across scopes that can push a term outside it.


The occur check
=================

Unlike Prolog, unification performs the **occur check** by default: assigning
a variable to a term that contains itself is rejected instead of building a
cyclic term. ``ground_term T`` checks that ``T`` has no unification variables
left in it at all — useful to assert a computation really finished, e.g.
before serializing a term. Turning the occur check off for one predicate is
:doc:`../compatibility` (``:nooc``); doing so can build a cyclic term, which
``ground_term`` (and most other traversals) will not terminate on.


The wildcard ``_``
====================

``_`` is a true wildcard, not a variable: every occurrence is independent, so
two ``_`` in the same head are never forced to be equal, unlike a repeated
named variable — see the Example below.


Example
=======

.. elpi:: ../code/wildcard.elpi
   :assert: same 1 2 fails, as expected\nany 1 2 succeeds, as expected
