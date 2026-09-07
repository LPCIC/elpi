#########################
Constraint handling rules
#########################

A goal can be **suspended** instead of solved: it becomes a **constraint**,
kept in the *constraint store* until it is woken up. **Constraint handling
rules** (CHR) inspect that store as a whole: they can drop constraints or spawn
new goals. This chapter is the syntax; the execution model — how the store
evolves, how rules fire — is :doc:`../semantics/chr`.


The constraint block
====================

A ``constraint`` block names a **clique** of predicates and holds the rules that
act on their constraints:

.. code-block:: elpi

   constraint even odd {
     rule (even X) (odd X) <=> false.
   }

The ``rule`` keyword may appear **only** inside such a block. The cliques of the
program must be pairwise disjoint, or Elpi raises *overlapping constraint
cliques*.

An optional **context filter**, written before ``?-``, lists further predicates
whose rules are retained in the context a constraint carries with it (by
default a resumed constraint keeps only the rules of its own clique):

.. code-block:: elpi

   constraint ctx ?- infer {
     % rules for `infer`; a resumed `infer` constraint also keeps the `ctx` rules
   }

The ``?-`` is omitted when the filter is empty.


Rules
=====

A rule has four parts, every one optional except the ``rule`` keyword itself:

.. code-block:: text

   rule  TO-MATCH  \ TO-REMOVE  | GUARD  <=> NEW-GOAL .

* **TO-MATCH** and **TO-REMOVE** are sequences of :ref:`sequent patterns
  <chr-sequents>` matched against the constraints in the store. A constraint
  matched to the left of ``\`` stays in the store; one matched to its right is
  taken out. With no ``\`` nothing is removed, and the rule fires at most once
  for a given set of matched constraints.
* **GUARD**, after ``|``, is a goal that must succeed for the rule to fire. The
  choice is then committed: no later rule is tried on those goals.
* **NEW-GOAL**, after ``<=>``, is a sequent run as a fresh goal.

So ``rule (even X) (odd X) <=> false`` runs ``false`` — which fails — whenever
the store holds ``even X`` and ``odd X`` for one ``X``. ``:name "…"`` (for trace
output) and ``:if "…"`` (:doc:`../features/conditional-compilation`) may precede
a rule.


.. _chr-sequents:

Sequent patterns
================

A sequent pattern is one of:

* ``Goal`` — matches a constraint, ignoring the hypotheses it carried;
* ``(Context ?- Goal)`` — also matches those hypotheses. ``Context`` is the
  **list** of rules that ``==>`` (or ``=>``) had added when the constraint was
  suspended, ordered most-recently-added first — so ``Context``'s head is the
  highest-priority rule. It holds only the rules for the predicates the
  context filter admits: the clique's own, plus any listed before ``?-`` in
  the ``constraint`` block;
* ``(Eigen :> Context ?- Goal)`` — also matches ``Eigen``, the list of
  eigenvariables (the ``pi``-introduced constants) the constraint lives under.

``Context`` and ``Eigen`` are ordinary patterns and may bind variables used in
the guard and the new goal.

Every unification variable inside a matched constraint is **frozen**: replaced
by a constant the rule cannot assign. This is what makes a rule *match* the
store rather than unify with it. A frozen variable is shown to the rule as
``uvar K L`` (the ``uvar`` head pattern — :doc:`../features/modes`) — ``K``
names it, ``L`` is the list of bound variables in its scope — and two
``uvar K …`` with the same ``K`` are the same variable.

.. code-block:: elpi

   constraint infer {
     % a hole has one type: two `infer` constraints about the same
     % unification variable K, in the same context G, must agree on the type
     rule (G ?- infer (uvar K _) T1)
        \ (G ?- infer (uvar K _) T2)
        <=> (T1 = T2).
   }

Each matched constraint is frozen into its own space of names, so with two
*different* context patterns the rule has to relate the terms across them
itself; see :doc:`../semantics/chr`.


Generating a constraint
=======================

``declare_constraint`` turns a goal into a **constraint** and puts it in the
store. The goal must be a **function** (a ``func`` signature,
:doc:`type-declarations`) — a relational predicate is rejected. The constraint
is suspended on one or more **keys**, which must be unification variables (or
``_``):

.. code-block:: elpi

   declare_constraint (even X) [X]

The constraint sits in the store until one of its keys is assigned, then runs
as an ordinary goal again. A key given as ``_``, or a constraint keyed on the
empty list, is never resumed. Several keys may be passed as one list —
``[X, Y]`` — or as separate arguments.

Every unification variable that occurs in the constraint should be among the
keys; an assignment to an omitted one will not wake it. Elpi does not check
this yet (`issue #441 <https://github.com/LPCIC/elpi/issues/441>`_).

The idiom is a rule that fires while the interesting argument is still a
variable, matched with the ``uvar`` pattern (:doc:`../features/modes`), and
suspends:

.. code-block:: elpi

   func even int.
   even (uvar as X) :- !, declare_constraint (even X) [X].
   even 0 :- !.
   even N :- N > 0, !, M is N - 2, even M.

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


Example
=======

.. elpi:: ../code/chr.elpi
   :assert: group 1 GCD is 11\ngroup 2 GCD is 7
