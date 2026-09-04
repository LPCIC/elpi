####################
The constraint store
####################

The constraint store introduced in :doc:`constraints` is a **multiset** of
constraints — each one a suspended goal, plus the hypotheses it carried and
the variables that trigger its resumption. A constraint handling rule
(:doc:`../syntax/constraint-handling-rules` for its syntax) inspects that
multiset as a whole. This chapter is what the store actually holds, and in
what order its rules are tried.


Frozen variables
================

A constraint handling rule *matches* the store, it never unifies with it — the
whole point of ``declare_constraint`` is to stop guessing values for a hole,
not to let a CHR rule do it instead. So every unification variable occurring
in a matched constraint is **frozen**: replaced with a fresh constant that no
rule can assign. A frozen variable ``F``, with bound variables ``x`` and ``y``
in its scope, is shown to rules as ``uvar f [x, y]`` for a fresh constant
``f`` — this reification is what lets a rule pattern name the identity of a
hole (``K`` in ``uvar K _``, see :doc:`../syntax/constraint-handling-rules`)
and inspect its scope, without any risk of assigning it. Each matched
constraint is frozen into its *own*, disjoint space of names, so that terms
coming from two different constraints never accidentally share a fresh
constant.


Triggers and clustering
========================

A rule is only ever tried against constraints that could plausibly be related:
those whose trigger — the key list given to ``declare_constraint`` — has a
non-empty intersection with the constraint that was just declared or resumed.
A constraint keyed on ``_`` is never resumed (``_`` can never be assigned),
but ``_`` is a single, shared placeholder, so passing it as one of several
keys — ``declare_constraint (even X) [_, X]`` — is a way to force two
otherwise unrelated constraints to be considered together by CHR without
expecting either to itself trigger a resumption. A constraint keyed on ``[]``
has no trigger at all: it is never resumed, and — having nothing to share — it
is never considered jointly with anything else either.


The refined operational semantics
==================================

As soon as a constraint ``C`` is declared or resumed, Elpi looks for a rule to
fire, following the *refined operational semantics* of
:ref:`Duck, Stuckey, García de la Banda & Holzbaur, 2004 <bib-chr2004>`
(:doc:`formal-semantics` gives the formal, rather than 8-step informal,
version of exactly this procedure — following, in turn,
:ref:`Guidi, Sacerdoti Coen & Tassi, 2019 <bib-tassi2019>`):

1. every rule of ``C``'s clique is considered, in the order it was written;
2. every constraint in the store whose trigger intersects ``C``'s is
   collected — call that set ``CS``;
3. for a rule with :math:`n` patterns, **every** way of picking :math:`n - 1`
   constraints from ``CS`` and placing ``C`` among them is tried — the store
   is a multiset, so a rule with several patterns can fire once per ordering
   of the same constraints;
4. the candidates are frozen (see above);
5. each frozen sequent is matched against the rule's corresponding pattern —
   on a mismatch, this candidate is abandoned and the next one is tried;
6. the terms of the candidates, until now living in disjoint name spaces, are
   spread into their union;
7. the guard runs — on failure, the next candidate or rule is tried; on
   success, the choice is **committed**: no further candidate or rule is
   tried for this ``C``;
8. the new goal, if any, is resumed immediately, before any other active
   goal.

Step 3 is the one most likely to surprise: with two matching constraints in
the store and a rule with no ``\``, a two-pattern rule fires **once per
ordering** of them, since removing nothing leaves both still eligible for the
next combination:

.. elpi:: ../code/chr-permutations.elpi
   :assert: declare c 1\nrule 2 on 1\ndeclare c 2\nrule 1 on 2 1\nrule 1 on 1 2\nrule 2 on 2

``rule 1`` fires on ``(c 2) (c 1)`` and again on ``(c 1) (c 2)``. Removing one
of the two constraints (``rule (c N) \ (c M) <=> …``) breaks the symmetry,
since the removed copy is no longer in the store for the second permutation;
a guard such as ``N < M`` breaks it just as well, by rejecting one of the two
orderings.


Cliques fix what a rule can see
================================

A clique (:doc:`../syntax/constraint-handling-rules`) is the fixed set of
predicates a group of rules is allowed to talk about — step 1 above only
considers the rules of ``C``'s own clique, which is why two cliques must be
disjoint: a rule could otherwise be reached from two unrelated triggers. The
context filter widens only what a *resumed* goal remembers of the hypothetical
rules it was suspended under, not which CHR rules apply to it.


Example
=======

Elpi has no built-in global variable, but the constraint store — a place that
outlives individual goals and honours backtracking — makes it easy to build
one on top of CHR:

.. elpi:: ../code/global-state.elpi
   :assert: N = 2
