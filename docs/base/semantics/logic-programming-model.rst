###########################
The logic programming model
###########################

Elpi is Prolog's model of rules and backtracking search, extended with
λProlog's support for syntax with binders. This chapter is that model — how a
query is solved and what a rule means. The concrete syntax is the Syntax part
of this manual, cross-referenced throughout.


Elpi vs Prolog
===============

Three things set the model apart from an imperative language: data is built
from **algebraic data types** (:doc:`../syntax/type-declarations`); code is a
set of **rules**, each a self-contained unit of meaning; and rules are tried
by **backtracking** search.

A rule's **head** drives its selection: it is *unified* with the goal,
possibly assigning the rule's own variables so that head and goal become
syntactically equal — unification computes the smallest such assignment. The
head need not be linear: a variable may occur more than once in it, so

.. code-block:: elpi

   pred symmetric tree.
   symmetric leaf.
   symmetric (node _ T T).

succeeds only on a tree that is empty or has two identical subtrees: the
second rule's head only unifies with a ``node`` whose two children are the
very same term.

Several rules may match the same goal; Elpi tries them all, in order,
backtracking into the next one on failure. The only control over this search
is the cut ``!`` (:doc:`../syntax/inference-rules-and-queries`), and it is a
*hard* cut: besides discarding the rule's remaining alternatives, it also
discards any alternative solution left to compute for the premises already
solved earlier in the same rule.

A rule is meaningful on its own: adding or removing one from a program is a
well-defined operation, unlike an assignment or a function definition, which
only make sense in a larger context — much like adding or removing an axiom
from a proof system. This is why the order in which rules are accumulated,
and — once cut is admitted — their relative order, matters, and why
:doc:`../syntax/file-structure-and-attributes` lets a rule be named and
placed among its siblings.


Elpi vs λProlog
================

λProlog adds **binders**: an object-language variable is represented by the
programming language's own bound variable — Higher-Order Abstract Syntax, or
*λ-tree syntax*. A simply-typed λ-calculus term is declared as

.. code-block:: elpi

   kind tm type.
   type app tm -> tm -> tm.
   type lam (tm -> tm) -> tm.

``lam`` takes an Elpi function ``tm -> tm``: the identity ``λx.x`` is written
``lam x\ x``, and applying that function to a term substitutes it for the
bound ``x`` — no substitution code has to be written. A bound variable such as
``x`` is not a unification variable: it can never be assigned, only
substituted for, and it is fresh — distinct from every other name in scope.

Type-checking this calculus needs one ingredient a Prolog rule cannot express
on its own: a rule that only holds for the duration of one bound variable's
scope. ``pi`` introduces a fresh constant for the duration of a goal, and
``=>`` adds a rule for the duration of a goal — together they give a bound
variable exactly the context it needs. Types are declared the same way as
terms, with one constructor ``arr`` for the function space:

.. code-block:: elpi

   kind ty type.
   type arr ty -> ty -> ty.

   pred of tm -> ty.
   of (app H A) T :- of H (arr S T), of A S.
   of (lam F) (arr S T) :- pi c\ of c S => of (F c) T.

To type-check ``lam F``: assume a fresh constant ``c`` stands for the bound
variable, add the rule ``of c S`` — valid only for the rest of this goal —
and check that the body ``F c`` (the function applied to ``c``) has type
``T``. The application rule alone is a Horn clause, as in Prolog; the
abstraction rule genuinely needs the ``∀`` and the nested ``⇒`` of a
**Hereditary Harrop formula** — the richer logic λProlog (and so Elpi) is
built on. A rule added by ``=>`` is called *dynamic*, or *hypothetical*, and —
unlike Prolog's ``assert``/``retract`` — its scope is exactly the goal that
added it, not the rest of the program (:doc:`../features/hypothetical-rules`).

Running the type checker on ``λx.λy.x`` infers a type without committing to
what ``x`` and ``y`` stand for:

.. code-block:: elpi

   goal> Fst = (lam x\ lam y\ x), of Fst Ty.
   Success:
     Fst = lam c0 \ lam c1 \ c0
     Ty = arr X0 (arr X1 X0)

This is as far as λProlog alone goes. Elpi is meant to type-check *incomplete*
terms too — the ones an interactive prover's elaborator works with, full of
holes still to be filled in. Running the checker above on ``of X T``, where
``X`` is completely unknown, never terminates: the first rule matches ``X``
against ``app H1 A1`` for fresh ``H1``, ``A1``, produces the subgoal
``of H1 (arr S1 T1)``, and the same rule matches again, forever. Avoiding this
— suspending on a hole instead of guessing a shape for it — is
:doc:`constraints`.


Example
=======

A program is a set of rules; a rule fires when its head unifies with the
goal, producing the premises as new goals; the search backtracks over the
rules.

.. elpi:: ../code/family.elpi
   :assert: bob is older than alice
