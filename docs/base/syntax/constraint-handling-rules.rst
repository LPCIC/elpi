#########################
Constraint handling rules
#########################

A goal can be *suspended* instead of solved: it becomes a *constraint*, and
sits in the *constraint store* until it is woken up. *Constraint handling
rules* (CHR) look at that store as a whole, and can drop constraints from it
and spawn new goals. The syntax has three parts: the ``constraint`` block, the
rules inside it, and the ``declare_constraint`` builtin that puts a goal in
the store. How the store then evolves and how rules fire is covered in
:doc:`../semantics/chr`.


The constraint block
====================

A ``constraint`` block names a *clique* of predicates and holds the rules
that act on their constraints:

.. code-block:: elpi

   constraint even odd {
     rule (even X) (odd X) <=> false.
   }

The ``rule`` keyword may appear only inside such a block. The cliques of a
program must be pairwise disjoint.

A resumed constraint carries a context with it: the hypothetical rules that
were in force when it was suspended (see `Sequent patterns`_ below). By
default that context is trimmed to the rules of the constraint's own clique.
An optional *context filter*, written before ``?-``, names further predicates
whose rules are kept as well:

.. code-block:: elpi

   constraint ctx ?- infer {
     % rules for `infer`; a resumed `infer` constraint also keeps
     % the rules it accumulated for `ctx`
   }

The ``?-`` is omitted when the filter is empty, as in the ``even odd`` block
above.


Rules
=====

A rule has four parts. Only the ``rule`` keyword itself is required; each of
the others may be left out:

.. code-block:: text

   rule  TO-MATCH  \ TO-REMOVE  | GUARD  <=> NEW-GOAL .

*TO-MATCH* and *TO-REMOVE* are sequences of :ref:`sequent patterns
<chr-sequents>`, matched against the constraints in the store. A constraint
matched on the left of the ``\`` stays in the store; one matched on its right
is taken out. With no ``\`` at all, nothing is removed, and the rule fires at
most once for each *ordering* of the constraints it matches, so a rule that
only adds goals does not loop. A two-pattern rule with two matching
constraints in the store therefore fires twice, once per ordering of the
pair, not once; :doc:`../semantics/chr` works this through.

*GUARD*, after the ``|``, is a goal that must succeed for the rule to fire.
Once it does, the choice is committed: no later rule is tried on the same
constraints.

*NEW-GOAL*, after the ``<=>``, is a sequent (see below) that is run as a
fresh goal when the rule fires.

So ``rule (even X) (odd X) <=> false`` runs the goal ``false``, which fails,
whenever the store holds both ``even X`` and ``odd X`` for one ``X``; because
a rule that has fired is not reconsidered, that failure is final. A rule may
be preceded by ``:name "…"`` (naming it for trace output) and ``:if "…"``
(:doc:`rule-attributes`).


.. _chr-sequents:

Sequent patterns
================

Elpi manages a context for every goal: the eigenvariables introduced by
``pi`` and the hypothetical rules introduced by ``==>``. A suspended goal
therefore is not a bare predicate but a sequent, ``Eigen ▷ Context ⊢ Goal``,
and a sequent pattern chooses how much of that to match:

* ``Goal`` matches only the goal, ignoring the eigenvariables and
  hypotheses the constraint carried;
* ``(Context ?- Goal)`` also matches the hypotheses. ``Context`` is the
  list of rules added by implication before the constraint was suspended,
  ordered most-recently-added first, so its head is the highest-priority
  rule. It holds only the rules for the predicates the context filter admits:
  the clique's own, plus any named before ``?-`` in the ``constraint`` block;
* ``(Eigen :> Context ?- Goal)`` also matches ``Eigen``, the list of
  eigenvariables (the ``pi``-introduced constants) the constraint lives
  under.

``Context`` and ``Eigen`` are ordinary patterns: they may be ``_``, a
variable, or a list pattern, and any variable they bind is in scope in the
guard and in the new goal.

Every unification variable inside a matched constraint is *frozen*: replaced
by a fresh constant that the rule cannot assign. Freezing is what makes a
rule *match* the store rather than unify with it: the non-linear ``K`` in the
rule below does not merge two unrelated constraints, it only fires when two
constraints really are about the same variable. A frozen variable is shown to
the rule through the ``uvar`` head pattern
(:doc:`../features/unification-and-variables`) as ``uvar K L``, where ``K``
identifies it and ``L`` is the list of bound variables in its scope; two
``uvar K …`` with the same ``K`` are the same variable.

When holes never appear under a binder, the "a hole has one type" rule needs
no context at all: keep the first typing, unify the second with it.

.. code-block:: elpi

   constraint infer {
     rule (infer (uvar K _) T1)
        \ (infer (uvar K _) T2)
        <=> (T1 = T2).
   }

Once holes can occur under binders, the same hole shows up in different
contexts, and the two types live in different scopes. Each matched constraint
is frozen into *its own* space of names (the ``Eigen`` lists of two matched
sequents are disjoint), so the rule must relate the terms across them itself,
in the guard, before it can compare them. This is the rule coq-elpi's
elaborator actually uses for uniqueness of typing:

.. code-block:: elpi

   constraint declare-evar evar decl def cache rm-evar {
     rule (E1 :> G1 ?- evar _ T1 (uvar K L1))         % K's declared type, in scope L1
        \ (E2 :> G2 ?- evar _ T2 (uvar K L2))         % a use of K, in scope L2
        | (canonical? L1, utc L1 T1 L2 T2 Condition)  % relocate T1 into L2's scope,
                                                      % producing a goal `Condition`
       <=> (E2 :> G2 ?- Condition).                   % run it under the using
   }                                                  % sequent's eigenvars and hypotheses

The guard ``utc`` ("uniqueness of typing") walks ``L1`` and ``L2`` in step,
substituting the canonical eigenvariables for the ones actually supplied, and
hands back ``Condition``, the goal that checks the two relocated types
agree. ``<=> (E2 :> G2 ?- Condition)`` then runs that goal back inside the
second sequent's context, where its eigenvariables and hypotheses are in
scope again. The full treatment, for a type theory where terms occur in
types, is given by :ref:`Guidi, Sacerdoti Coen & Tassi <bib-tassi2019>`; see
also :doc:`../semantics/chr`.


Generating a constraint
=======================

``declare_constraint`` turns a goal into a constraint and puts it in the
store. The goal must be a *function*: it needs a ``func`` signature
(:doc:`type-declarations`), and a relational predicate is rejected. The
constraint is suspended on one or more *keys*, each of which must be a
unification variable (or ``_``):

.. code-block:: elpi

   declare_constraint (even X) [X]

The constraint sits in the store until one of its keys is assigned, and then
runs as an ordinary goal again. A key given as ``_``, and a constraint keyed
on the empty list, are never resumed. Several keys may be passed as one list,
``[X, Y]``, or as separate arguments.

Every unification variable that occurs in the constraint should be among the
keys; an assignment to one that is left out will not wake the constraint.
Elpi does not check this yet (`issue #441
<https://github.com/LPCIC/elpi/issues/441>`_).

The usual idiom is a rule that fires while the interesting argument is still a
variable, matched with the ``uvar`` pattern
(:doc:`../features/unification-and-variables`), and suspends the goal on it:

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

A larger program using every part of the syntax above is Euclid's GCD, with
each ``gcd`` fact reduced against the others in its group until one number is
left:

.. elpi:: ../code/chr.elpi
   :assert: group 1 GCD is 11\ngroup 2 GCD is 7
