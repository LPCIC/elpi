###########################
Inference rules and queries
###########################

A program is a sequence of *rules* and directives (``data``, ``symb``,
``pred``, ``accumulate``, ``namespace { … }``, …). This chapter covers the
syntax of a rule, of the *goals* that make up a rule's body, and of the
queries run against a program. The rules described here are the program's
*inference rules*: they are what the proof search chains together. The
*constraint handling rules* that act on suspended goals are a separate
construct with a syntax of their own — see :doc:`constraint-handling-rules`.


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
them — so the fact ``same-two [T, T].`` holds for any ``T``, a different
``T`` on each call.

Several rules for the same predicate are *alternatives*. The search tries
them in source order and backtracks into the next one whenever a later goal
fails. That order can be adjusted with attributes (see below).


Goals
=====

The body of a rule, and a query, are *goals*. A goal is one of:

* an atom, ``p t1 … tn`` — a call;
* ``g1, g2`` — conjunction (``&`` is an accepted synonym, and a list
  ``[g1, g2, g3]`` also means ``g1, g2, g3``);
* ``g1 ; g2`` — disjunction;
* ``H ==> g`` — solve ``g`` with the extra rule ``H`` added to the program for
  the duration of ``g``; ``[H1, H2] ==> g`` adds several, and is read
  ``H2 ==> (H1 ==> g)`` so that ``H1`` is the one tried first. ``=!=>`` is
  ``==>`` with an automatic tail cut on ``H``. See
  :doc:`../features/hypothetical-rules`;
* ``pi x\ g`` — solve ``g`` with a fresh constant standing for ``x``;
  ``sigma X\ g`` — with a fresh unification variable — see
  :doc:`../features/binders-and-hoas`;
* ``!`` — cut — see :doc:`../features/control-and-cut`.

``=>`` is the traditional λProlog spelling of the same implication as ``==>``.
The two differ only in precedence. ``==>`` binds looser than ``,``, so
``a, b ==> c, d`` reads ``a, (b ==> (c, d))``; ``=>`` binds tighter, so
``a, b => c, d`` reads ``a, (b => c), d``, which makes ``a`` available to
``b`` but not to ``c`` — usually a mistake, and Elpi prints a warning for it.
This manual writes ``==>`` throughout.

Because ``\`` extends its body as far right as possible, a ``pi`` or ``sigma``
inside a conjunction swallows the goals after it: ``a, pi x\ b, c`` means
``a, (pi x\ (b, c))``. Parenthesise the binder to keep a later goal out of the
fresh constant's scope.

.. elpi:: ../code/pi-scope.elpi
   :assert: inside sees 1 name.s.\nafter sees 0 name.s.

Naming a subterm of the head
============================

``(t as N)`` inside a rule head binds ``N`` to whatever ``t`` matched, so the
body can name that subterm without describing it a second time. The
parentheses are part of the syntax (:doc:`terms-and-operators`), and ``as``
may wrap an argument or a piece of one, but not the head as a whole:

.. code-block:: elpi

   whd (lam F as T) T. % a lambda is already in weak head normal form

Attributes
==========

An attribute is written before the rule, ``:``-prefixed, and may sit on its own
line:

.. code-block:: elpi

   :name "step" :if "DEBUG"
   step X :- ...

``:name``, ``:before``, ``:after``, ``:replace`` and ``:remove`` control
where the rule sits among the alternatives (:doc:`../features/rule-grafting`),
and ``:if`` keeps the rule only when a given compiler variable is defined
(:doc:`../features/conditional-compilation`).

Attributes that describe the predicate itself, rather than one of its rules —
``:index``, ``:functional`` and the like — go on the ``pred`` / ``func``
signature instead, see :doc:`type-declarations`.


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
* from a host application, through the OCaml API — see :doc:`../embedding`.

``?-`` is not a query prefix in Elpi, as it is in some Prolog systems; it is
the sequent separator used in ``constraint`` blocks and CHR rules
(:doc:`constraint-handling-rules`).


Example
=======

.. elpi:: ../code/rules.elpi
   :assert: alice has 2 descendants
