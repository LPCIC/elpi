#########################
Unification and variables
#########################

A unification variable stands for a term not yet known; it is assigned at
most once, and backtracking undoes the assignment
(:doc:`../semantics/logic-programming-model`, :doc:`../semantics/constraints`).
The flags and builtins around that mechanism follow: inspecting a variable,
the pattern fragment, the occur check, and the wildcard.


Unification variable inspection
===============================

A rule head does not normally fire on an unassigned variable: an input
argument is *matched*, and matching against a rigid pattern would have to
assign the hole (:doc:`../semantics/constraints`). To write a rule that *does*
fire on a hole, match it in the head with the ``uvar`` keyword. It comes in a
few shapes:

* ``uvar`` matches any hole;
* ``uvar as X`` matches a hole and binds ``X`` to the whole term, for the
  rest of the rule to use:

  .. code-block:: elpi

     even (uvar as X) :- !, declare_constraint (even X) [X].

* ``uvar Hd Args`` matches an *applied* hole, binding ``Hd`` to the bare
  variable and ``Args`` to the list of arguments it is applied to (the names
  in scope where it was created, followed by any it is explicitly applied
  to);
* ``uvar Hd Args as X`` is the same, and binds ``X`` to the whole applied
  term.

.. elpi:: ../code/uvar-pattern.elpi
   :assert: unapplied hole: X\d+\napplied hole: X\d+ c\d+ c\d+ -- head X\d+ args \[c\d+, c\d+\]\nnot a hole: 42

The builtin ``var`` is the same decomposition from a rule body, on a term the
head did not already take apart with ``uvar``: ``var V`` checks that ``V`` is
unassigned, and ``var V Hd Args`` splits an applied one into its head ``Hd``
and its argument list ``Args``.


The pattern fragment
=====================

Elpi's unification is decidable and well-behaved as long as it stays within
the *pattern fragment* (Lλ, Miller's higher-order patterns,
:ref:`Miller, 1991 <bib-miller91>`): a unification variable applied only to
*distinct* bound names. Outside of it, unification can have several, or
infinitely many, most general solutions. Elpi does not guess: by default it
aborts with an error on such a problem. The deprecated
``-delay-problems-outside-pattern-fragment`` flag makes it suspend the problem
as a constraint instead, the way Teyjus does (:doc:`../compatibility`).

``distinct_names L`` checks that ``L`` is a list of pairwise-distinct bound
names, so, given the ``Args`` from ``var`` above, it tells whether a
variable is currently in the pattern fragment:

.. code-block:: elpi

   pred in-pattern-fragment any.
   in-pattern-fragment X :- var X _ Args, distinct_names Args, !.
   in-pattern-fragment _ :- print "outside the pattern fragment".

A variable's own arguments, the names in scope when it was created via
``pi``/``sigma``, are always distinct, so a *freshly allocated* variable is
always in the fragment; it is only *later* applications, unification, or
explicit reuse across scopes that can push a term outside it.


The occur check
=================

Unification performs the *occur check* by default: assigning a variable to a
term that already contains it is rejected, rather than building a cyclic
term. Most Prolog systems default the other way, and Elpi's choice is one of
the deliberate departures collected in :doc:`../compatibility`.

``ground_term T`` checks that ``T`` holds no unification variables at all,
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
named variable:

.. elpi:: ../code/wildcard.elpi
   :assert: same 1 2 fails, as expected\nany 1 2 succeeds, as expected
