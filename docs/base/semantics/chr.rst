####################
The constraint store
####################

The constraint store introduced in :doc:`constraints` is a *multiset* of
constraints, each one a suspended goal together with the hypotheses it carried
and the variables that trigger its resumption. A constraint handling rule
(:doc:`../syntax/constraint-handling-rules` for its syntax) inspects that
multiset as a whole. What follows is what the store holds, and in what order
its rules are tried.


Frozen variables
================

A constraint handling rule *matches* the store, it never unifies with it. The
whole point of ``declare_constraint`` is to stop guessing values for a hole,
not to let a CHR rule guess one instead. So every unification variable
occurring in a matched constraint is *frozen*: replaced with a fresh constant
that no rule can assign. A frozen variable ``F``, with the bound variables
``x`` and ``y`` in its scope, is shown to rules as ``uvar f [x, y]`` for a
fresh constant ``f``. This reification is what lets a rule pattern name the
identity of a hole (``K`` in ``uvar K _``, see
:doc:`../syntax/constraint-handling-rules`) and read off its scope, with no
way of assigning it. Each matched constraint is frozen into its *own*,
disjoint space of names, so terms coming from two different constraints never
accidentally share a fresh constant.


Triggers and clustering
========================

A rule is only ever tried against constraints that could plausibly be
related: those whose trigger, the key list given to ``declare_constraint``,
has a non-empty intersection with the constraint that was just declared or
resumed. A constraint keyed on ``_`` is never resumed (``_`` can never be
assigned), but ``_`` is a single shared placeholder, so passing it as one of
several keys (``declare_constraint (even X) [_, X]``) forces two otherwise
unrelated constraints to be considered together by CHR without expecting
either to trigger a resumption on its own. A constraint keyed on ``[]`` has
no trigger at all: it is never resumed, and, sharing nothing, no
*multi-headed* rule ever considers it jointly with another constraint. A
*single-headed* rule needs no partner, so it is still tried on such a
constraint, once, when the constraint is declared. ``code/hindley-milner.elpi``
relies on this: it keys its ``overbar`` constraint on ``[]`` and generalizes
it with a single-headed rule.


Application of CHR rules
========================

As soon as a constraint ``C`` is declared or resumed, Elpi looks for a rule
to fire on it. It goes through the rules of ``C``'s clique from top to
bottom. For each rule it gathers the store constraints whose trigger overlaps
``C``'s, and tries every way of matching the rule's patterns against ``C``
placed among enough of those others; ``C`` may land in any one of the
patterns, not only the first. The candidate constraints are frozen first
(see above). If they all match their patterns and the guard then succeeds,
the rule fires: the constraints matched to the right of the ``\`` are removed
from the store, and the goal after ``<=>``, if any, is run at once, ahead of
any other pending goal. The choice is committed at that point: no other
rule, and no other way of matching this one, is tried for ``C``.

This is the *refined operational semantics* of
:ref:`Duck, Stuckey, García de la Banda & Holzbaur <bib-chr2004>`; it is given
precisely in :doc:`formal-semantics`, following in turn
:ref:`Guidi, Sacerdoti Coen & Tassi <bib-tassi2019>`.


Symmetric CHR rules
======================

The case most likely to surprise is a rule with no ``\``. With two matching
constraints in the store, a two-pattern rule fires *once per ordering* of
them: removing nothing leaves both in the store, still eligible when the next
combination is tried.

.. elpi:: ../code/chr-permutations.elpi
   :assert: declare c 1\nrule 2 on 1\ndeclare c 2\nrule 1 on 2 1\nrule 1 on 1 2\nrule 2 on 2

``rule 1`` fires on ``(c 2) (c 1)`` and then again on ``(c 1) (c 2)``.

A rule whose two patterns are of the *same* predicate and which removes
nothing is *symmetric*, and it is this matching-without-removing shape that
gets retried on every ordering of a pair. Removing one of the two matched
constraints (``rule (c N) \ (c M) <=> …``) breaks the symmetry: the removed
copy is gone from the store before the second ordering is tried, so the rule
fires only once, on whichever ordering comes up first (here ``(c 2) (c 1)``,
keeping ``c 2`` and removing ``c 1``). That kept constraint stays in the
store:

.. elpi:: ../code/chr-permutations-fixed.elpi
   :assert: declare c 1\nrule 2 on 1\ndeclare c 2\nrule 1 on 2 1\nrule 2 on 2

A guard such as ``N < M`` breaks the symmetry equally well, by rejecting one
of the two orderings rather than removing a constraint. Since either fix
works, and which one is correct depends on the rule, Elpi does not warn about
a symmetric pattern on its own.


Cliques fix what a rule can see
================================

A clique (:doc:`../syntax/constraint-handling-rules`) is the fixed set of
predicates a group of rules may talk about. Rule search only ever considers
the rules of ``C``'s own clique, which is why two cliques must be disjoint: a
rule could otherwise be reached from two unrelated triggers. The context
filter widens only what a *resumed* goal remembers of the hypothetical rules
it was suspended under, not which CHR rules may act on it.


A global variable built on CHR
================================

Elpi has no built-in global variable, but the constraint store, a place that
outlives individual goals and honours backtracking, makes it easy to build
one on top of CHR. The program below implements named global variables:
``get`` and ``set`` take the variable's name as a string, so several can
coexist. ``main`` initialises ``x`` and ``y``, reads ``x``, overwrites it,
and reads both again, so ``x``'s two reads print the old value then the new
one while ``y`` is unchanged:

.. elpi:: ../code/global-state.elpi
   :assert: x before: 2 x after: 3 y: 10
