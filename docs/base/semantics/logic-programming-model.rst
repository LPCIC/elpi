###########################
The logic programming model
###########################

This chapter describes how Elpi computes: how a query is reduced to smaller
goals, when a rule applies to a goal, and what a rule means on its own. The
surface syntax it refers to is the *Syntax* part of the manual, linked as it
comes up. Elpi's model is Prolog's — rules and backtracking search — with
λProlog's treatment of syntax that contains binders layered on top.


Elpi vs Prolog
===============

Elpi keeps Prolog's core. Data is built from constructors, which in Elpi are
declared and typed (:doc:`../syntax/type-declarations`) rather than used
freely as in Prolog. A program is a set of *rules*, each one a self-contained
unit of meaning. And the search is *backtracking*: rules are tried in order,
and when a goal fails the search retreats to the most recent still-open
choice and takes its next alternative.

Where Elpi departs from Prolog is in how a rule's *head* is matched against
the goal. Prolog *unifies* the two, instantiating variables on either side as
needed. Elpi does that only for a predicate's *output* arguments; its *input*
arguments are one-way *matched* instead — the pattern in the head may inspect
the goal, but it may not instantiate a variable that the goal left unbound.
Which arguments are which is fixed by the ``pred`` / ``func`` signature
(:doc:`../syntax/type-declarations`), and what the distinction buys you is
:doc:`../features/modes`. This one-way matching of input arguments is the same
mechanism as the *matching clauses* of :ref:`B-Prolog <bib-bprolog>`, though
Elpi marks it per argument in the signature rather than per clause.

A head need not be linear — a variable may occur in it more than once, which
forces the two positions to hold the same term:

.. code-block:: elpi

   pred symmetric tree.
   symmetric leaf.
   symmetric (node _ T T).

``symmetric`` succeeds on a tree that is a leaf, or a ``node`` whose two
children are the very same term; the repeated ``T`` in the second head is
what ties them together. (It does not recurse, so it does not check that the
children are themselves symmetric.)

Several rules may apply to one goal. Elpi tries them top to bottom and
backtracks into the next on failure. The only control over this search is the
cut, ``!`` (:doc:`../syntax/inference-rules-and-queries`), and Elpi's is a
*hard* cut: besides discarding the current rule's untried alternatives, it
also discards any alternative solutions still available for the premises
already solved earlier in the same rule.

A rule is meaningful in isolation: adding one to a program, or taking one
away, is a well-defined change — unlike an assignment or a function
definition, which only mean something in a larger context. It is closer to
adding or removing an axiom in a proof system. This is why the order in which
rules are accumulated matters, why — once cut is in play — their relative
order matters too, and why :doc:`../syntax/file-structure-and-attributes`
gives a rule a name and a place among its siblings.


Elpi vs λProlog
================

λProlog adds *binders*. An object-language variable is represented directly
by a bound variable of the programming language — a technique called
*Higher-Order Abstract Syntax*, or *λ-tree syntax*. A simply-typed
λ-calculus term is declared as

.. code-block:: elpi

   data tm.
   symb app tm -> tm -> tm.
   symb lam (tm -> tm) -> tm.

``lam`` takes an Elpi function of type ``tm -> tm``: the identity ``λx.x`` is
written ``lam x\ x``, and applying that function to a term substitutes the
term for the bound ``x`` — no substitution code has to be written. A bound
variable like ``x`` is not a unification variable: it can never be assigned,
only substituted for, and it is fresh, distinct from every other name in
scope.

Type-checking this calculus needs one ingredient a Prolog rule cannot express
on its own: a rule that holds only for the lifetime of one bound variable's
scope. ``pi`` introduces a fresh constant for the duration of a goal, and
``==>`` adds a rule for the duration of a goal; together they give a bound
variable exactly the context it needs. Types are declared like terms, with a
constructor ``arr`` for the function space:

.. code-block:: elpi

   data ty.
   symb arr ty -> ty -> ty.

   pred of tm -> ty.
   of (app H A) T :- of H (arr S T), of A S.
   of (lam F) (arr S T) :- pi c\ of c S ==> of (F c) T.

To type-check ``lam F``: introduce a fresh constant ``c`` for the bound
variable, add the rule ``of c S`` — in force only for the rest of this goal —
and check that the body ``F c``, the function applied to ``c``, has type
``T``. The application rule on its own is a Horn clause, exactly as in
Prolog; the abstraction rule genuinely needs the ``∀`` and the nested ``⇒``
of a *Hereditary Harrop formula*, the richer logic that λProlog, and so Elpi,
is built on. A rule added by ``==>`` is called *dynamic*, or *hypothetical*,
and — unlike Prolog's ``assert`` / ``retract`` — its scope is exactly the
goal that added it, never the rest of the program
(:doc:`../features/hypothetical-rules`).

Run on a closed term, the checker infers a type without committing to what
the bound variables stand for:

.. code-block:: text

   goal> Fst = (lam x\ lam y\ x), of Fst Ty.
   Success:
     Fst = lam c0 \ lam c1 \ c0
     Ty = arr X0 (arr X1 X0)

This is as far as λProlog alone goes. Elpi is meant to type-check *incomplete*
terms as well — the terms an interactive prover's elaborator manipulates,
still full of holes to be filled in. Ask the checker above for ``of X T``
with ``X`` an unknown hole and nothing useful happens: because the first
argument of ``of`` is an input, no rule head matches a bare variable, and the
goal simply fails. Make that argument unified instead — as plain λProlog,
with no modes, would — and it does worse: the first rule matches ``X``
against ``app H1 A1`` for fresh ``H1``, ``A1``, then against ``app H2 A2``
inside that, and so on without end. Neither outcome is what an elaborator
needs. The way out — suspend the goal on the hole until its shape is known,
instead of guessing — is :doc:`constraints`.


Example
=======

A program is a set of rules; a rule fires when its head matches the goal,
turning the rule's premises into new goals; the search backtracks over the
rules.

.. elpi:: ../code/family.elpi
   :assert: bob is older than alice
