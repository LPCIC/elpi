#########################
Constraint handling rules
#########################

A goal can be **suspended** instead of solved, kept in a *constraint store*, and
woken up later. **Constraint handling rules** (CHR) inspect that store as a
whole: they can drop suspended goals or spawn new ones. This chapter is the
syntax; the execution model — how the store evolves, how rules fire — is
:doc:`../semantics/chr`.


Suspending a goal
=================

``declare_constraint`` suspends a goal on one or more **keys**, which must be
unification variables (or ``_``):

.. code-block:: elpi

   declare_constraint (even X) [X]

The goal is parked until one of the keys is assigned, then run as an ordinary
goal. A key given as ``_``, or a goal keyed on the empty list, is never resumed.
Several keys may be passed as one list — ``[X, Y]`` — or as separate arguments.

The idiom is a rule that fires when the interesting argument is still a
variable, matched with the ``uvar`` pattern (:doc:`../features/modes`), and
suspends:

.. code-block:: elpi

   func even int.
   even (uvar as X) :- !, declare_constraint (even X) [X].
   even 0.
   even N :- N > 0, M is N - 2, even M.

At the top-level prompt a leftover constraint is printed after the solution;
``print_constraints`` prints the store at any point:

.. code-block:: text

   goal> declare_constraint (even X) [X].
   Success:
     X = X0
   Constraints:
    even X0  /* suspended on X0 */

   goal> declare_constraint (even X) [X], X = 1.
   Failure


The constraint block
====================

A ``constraint`` block names a **clique** of predicates and holds the rules that
act on their suspended goals:

.. code-block:: elpi

   constraint even odd {
     rule (even X) (odd X) <=> false.
   }

``rule`` may appear **only** inside such a block. The cliques of the program
must be pairwise disjoint, or Elpi raises *overlapping constraint cliques*.

An optional **context filter**, written before ``?-``, lists further predicates
whose rules are retained in the context a suspended goal carries with it (by
default a resumed goal keeps only the rules of its own clique):

.. code-block:: elpi

   constraint ctx ?- infer {
     % rules for `infer`; a resumed `infer` goal also keeps the `ctx` rules
   }

The ``?-`` is omitted when the filter is empty.


CHR rules
=========

A rule has four parts, each optional except the keyword:

.. code-block:: text

   rule  TO-MATCH  \ TO-REMOVE  | GUARD  <=> NEW-GOAL .

* **TO-MATCH** and **TO-REMOVE** are sequences of :ref:`sequent patterns
  <chr-sequents>` matched against suspended goals. Everything to the left of
  ``\`` is matched and kept; everything to its right is matched and removed —
  a *simpagation* rule. A rule with no ``\`` removes nothing: it only adds
  ``NEW-GOAL`` (a *propagation* rule) and fires at most once per combination of
  constraints.
* **GUARD**, after ``|``, is a goal that must succeed for the rule to fire.
  Firing is *committed choice*: once the guard passes, no later rule is tried
  on the same constraints.
* **NEW-GOAL**, after ``<=>``, is a sequent added as a fresh goal.

So ``rule (even X) (odd X) <=> false`` runs ``false`` — which fails — whenever
the store holds ``even X`` and ``odd X`` for one ``X``. ``:name "…"`` (for trace
output) and ``:if "…"`` (:doc:`../features/conditional-compilation`) may precede
a rule.

.. _chr-sequents:

Sequent patterns
================

A sequent pattern is one of

.. code-block:: text

   Goal
   ( Context ?- Goal )
   ( Eigen :> Context ?- Goal )

``Goal`` alone matches a suspended goal, ignoring the hypotheses it carried.
``Context`` matches those hypotheses — the rules added with ``=>`` that were in
scope at suspension — and ``Eigen`` matches the list of eigenvariables (the
``pi``-introduced constants) it lives under. ``Context`` and ``Eigen`` are
ordinary patterns and may bind variables used in the guard and the new goal.

A **frozen** unification variable of the suspended goal appears in a pattern as
``uvar K L``: ``K`` identifies the variable and ``L`` is the list of bound
variables in its scope. Freezing — turning those variables into constants a
rule cannot assign — is what makes a rule *match* the store rather than unify
with it; two ``uvar K …`` with the same ``K`` are the same variable.

.. code-block:: elpi

   constraint infer {
     % a hole has one type: two `infer` goals about the same unification
     % variable K, in the same context G, must agree on the type
     rule (G ?- infer (uvar K _) T1)
        \ (G ?- infer (uvar K _) T2)
        <=> (T1 = T2).
   }

Each matched constraint is frozen into its own space of names, so with two
*different* context patterns the rule has to relate the terms across them
itself; see :doc:`../semantics/chr`.


Example
=======

.. elpi:: ../code/chr.elpi
   :assert: group 1 GCD is 11\ngroup 2 GCD is 7
