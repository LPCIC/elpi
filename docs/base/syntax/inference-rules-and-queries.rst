###########################
Inference rules and queries
###########################

A program is a sequence of *rules* and directives (``data``, ``symb``,
``pred``, ``accumulate``, ``namespace { … }``, …). What follows is the syntax
of a rule, of the *goals* that make up a rule's body, and of the queries run
against a program. The rules here are the program's *inference rules*: they
are what the proof search chains together. The
*constraint handling rules* that act on suspended goals are a separate
construct with a syntax of their own (:doc:`constraint-handling-rules`).


Rules
=====

A rule is either a bare atom, called a *fact*, or an atom followed by ``:-``
and a body, called a *conditional rule*. Either way it ends with a full stop:

.. code-block:: elpi

   age alice 20.                              % a fact
   older P Q :- age P N, age Q M, N > M.      % a conditional rule

The head is an application ``p t1 … tn`` (or just ``p``). A conditional rule
reads "the head holds if the body holds". A rule's variables are universally
quantified over the whole rule, and every use of the rule gets a fresh set of
them, so the fact ``same-two [T, T].`` holds for any ``T``, a different ``T``
on each call.

Several rules for the same predicate are *alternatives*. The search tries
them in source order and backtracks into the next one whenever a later goal
fails. That order can be adjusted with attributes (see below).


Goals
=====

The body of a rule, and a query, are *goals*. A goal is one of:

* an atom, ``p t1 … tn``: a call;
* ``g1, g2``: conjunction (``&`` is an accepted synonym, and a list
  ``[g1, g2, g3]`` also means ``g1, g2, g3``);
* ``g1 ; g2``: disjunction;
* ``H ==> g``: solve ``g`` with the extra rule ``H`` added to the program for
  the duration of ``g``; ``[H1, H2] ==> g`` adds several, and is read
  ``H2 ==> (H1 ==> g)`` so that ``H1`` is the one tried first. ``=!=>`` is
  ``==>`` with a cut automatically appended to ``H``'s body (`Committing a
  hypothetical rule`_, below);
* ``pi x\ g``: solve ``g`` with a fresh constant standing for ``x``;
  ``sigma X\ g`` uses a fresh unification variable instead
  (:doc:`../features/binders-and-hoas`);
* ``!``: cut (:doc:`../features/control-and-cut`).

``=>`` is the traditional λProlog spelling of the same implication as ``==>``.
The two differ only in precedence. ``==>`` binds looser than ``,``, so
``a, b ==> c, d`` reads ``a, (b ==> (c, d))``; ``=>`` binds tighter, so
``a, b => c, d`` reads ``a, (b => c), d``, which makes ``b`` available to
``c`` but not to ``d``. That is usually a mistake, and Elpi prints a warning
when a ``=>`` appears as a non-final conjunct like this. This manual writes
``==>`` throughout.

Because ``\`` extends its body as far right as possible, a ``pi`` or ``sigma``
inside a conjunction swallows the goals after it: ``a, pi x\ b, c`` means
``a, (pi x\ (b, c))``. Parenthesise the binder to keep a later goal out of the
fresh constant's scope.

.. elpi:: ../code/pi-scope.elpi
   :assert: inside sees 1 name.s.\nafter sees 0 name.s.


Committing a hypothetical rule
==============================

``H =!=> G`` adds ``H`` for the duration of ``G`` with a cut appended to its
body: a rule ``head :- body`` becomes ``head :- body, !``, and a bare fact
``head`` becomes ``head :- !``. Once ``H`` yields its first solution the cut
fires, so ``G`` finds no choice point to backtrack into and no later rule of
the same predicate is tried. When ``H`` is a term the compiler can see it
appends the cut up front; when ``H`` is only known at run time (a variable
bound to a rule computed on the fly) the cut is appended dynamically, as the
rule is added.

The use for it is a ``func`` predicate handed an extra rule at run time. The
static rule ``copy X X`` alone lets ``copy a Z`` answer ``Z = a``; adding
``copy a b`` beside it creates a second solution, and the determinacy checker
(:doc:`../features/determinacy-checking`) rejects the ``func`` for that choice
point. ``=!=>`` removes it, so the program compiles and ``copy a Z`` has the
single solution ``copy a b``:

.. elpi:: ../code/tail-cut.elpi
   :assert: solutions of copy a: \[copy a b\]


Naming a subterm of the head
============================

A rule head can name a subterm with ``(t as N)`` (:doc:`terms`), so the body
refers to it without spelling it out again. In a head, ``as`` may wrap an
argument or a piece of one, but not the head as a whole:

.. code-block:: elpi

   whd (lam F as T) T. % a lambda is already in weak head normal form

Attributes
==========

An attribute is written ``:``-prefixed before the rule and may sit on its own
line:

.. code-block:: elpi

   :name "step" :if "DEBUG"
   step X :- ...

``:name``, ``:before``, ``:after``, ``:replace`` and ``:remove`` graft the
rule among its predicate's alternatives; ``:if`` keeps it only when a compiler
variable is defined; ``:untyped`` exempts it from the type checker. All of
them are described in :doc:`rule-attributes`. Attributes that describe the
*predicate* instead (``:index``, ``:functional`` and the like) go on the
``pred`` /
``func`` signature (:doc:`type-declarations`).


Queries
=======

A query is a goal run against a program:

* ``elpi prog.elpi -test`` runs the goal ``main``;
* ``elpi prog.elpi -exec p -- a b c`` runs ``p ["a", "b", "c"]`` (the predicate
  receives a single ``list string``);
* ``elpi prog.elpi`` with a goal typed or piped on standard input opens a
  ``goal>`` prompt, reads one goal, prints the value bound to each of its
  unification variables in the first solution, then asks whether to look for
  another;
* from a host application, through the OCaml API (:doc:`../embedding`).

``?-`` is not a query prefix in Elpi, as it is in some Prolog systems; it is
the sequent separator used in ``constraint`` blocks and CHR rules
(:doc:`constraint-handling-rules`).

Facts, conditional rules and a query together:

.. elpi:: ../code/rules.elpi
   :assert: alice has 2 descendants
