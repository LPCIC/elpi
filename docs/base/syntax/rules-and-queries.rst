#################
Rules and queries
#################

A program is a sequence of **rules** and directives (``kind``, ``type``,
``pred``, ``accumulate``, ``namespace { … }``, …). This chapter is the syntax
of rules and of the **goals** that make up their bodies and the queries you run
against them.


Rules
=====

A rule is an atom — a *fact* — or an atom and a body separated by ``:-`` — a
*conditional rule* — terminated by ``.``:

.. code-block:: elpi

   age alice 20.                              % a fact
   older P Q :- age P N, age Q M, N > M.      % a conditional rule

The head is an application ``p t1 … tn`` (or just ``p``). A conditional rule
reads "the head holds if the body holds". Its variables are universally
quantified over the whole rule, and every use of the rule gets fresh ones — so
``same-two [T, T].`` is a fact for *any* ``T``.

Several rules for the same predicate are **alternatives**, tried top to bottom;
the search backtracks into them. That order can be adjusted with attributes
(see below).


Goals
=====

The body of a rule, and a query, are *goals*. A goal is one of:

* an atom, ``p t1 … tn`` — a call;
* ``g1, g2`` — conjunction (``&`` is an accepted synonym, and a list
  ``[g1, g2, g3]`` also means ``g1, g2, g3``);
* ``g1 ; g2`` — disjunction;
* ``H ==> g`` — solve ``g`` with the extra rule ``H`` added to the program for
  the duration of ``g``; ``[H1, H2] ==> g`` adds several and reads
  ``H2 ==> H1 ==> g``. ``=>`` is the traditional λProlog spelling and means the
  same, but binds differently: ``a, b ==> c, d`` reads ``a, (b ==> (c, d))``
  whereas ``a, b => c, d`` reads ``a, (b => c), d`` — a frequent mistake, so
  Elpi warns about the second and the manual uses ``==>``. ``=!=>`` is like
  ``==>`` but also gives the extra rule a tail cut. See
  :doc:`../features/hypothetical-rules`;
* ``pi x\ g`` — solve ``g`` with a fresh constant standing for ``x``;
  ``sigma X\ g`` — with a fresh unification variable — see
  :doc:`../features/binders-and-hoas`;
* ``!`` — cut — see :doc:`../features/control-and-cut`.

Because ``\`` extends its body as far right as possible, a ``pi`` or ``sigma``
inside a conjunction swallows the goals after it: ``a, pi x\ b, c`` means
``a, (pi x\ (b, c))``. Parenthesise the binder to keep a later goal out of the
fresh constant's scope.

.. elpi:: ../code/pi-scope.elpi
   :assert: inside sees 1 name.s.\nafter sees 0 name.s.

Naming a subterm of the head
============================

``(t as N)`` in a rule head binds ``N`` to whatever ``t`` matched, so the body
can refer to it. It cannot wrap the whole head.

.. code-block:: elpi

   whd (lam F as T) T. % a lambda is in weak head normal form

Attributes
==========

An attribute is written before the rule, ``:``-prefixed, and may sit on its own
line:

.. code-block:: elpi

   :name "step" :if "DEBUG"
   step X :- ...

``:name``, ``:before``, ``:after``, ``:replace`` and ``:remove`` control where
the rule goes among the alternatives (:doc:`../features/rule-grafting`);
``:if`` keeps the rule only when a compiler variable is defined
(:doc:`../features/conditional-compilation`). 

Attributes that describe the
predicate itself (``:index``, ``:functional``, …) go on its ``pred`` / ``func``
signature instead — :doc:`declarations-and-attributes`.


Queries
=======

A query is a goal run against a program:

* ``elpi prog.elpi -test`` runs the goal ``main``;
* ``elpi prog.elpi -exec p -- a b c`` runs ``p ["a", "b", "c"]`` (the predicate
  receives a single ``list string``);
* ``elpi prog.elpi`` with a goal on standard input opens a ``goal>`` prompt and
  prints the unification variables of the first solution, then offers to look
  for more;
* from a host application, through the OCaml API — see :doc:`../embedding`.

``?-`` is **not** a query prefix in Elpi; it is the sequent separator used in
``constraint`` blocks and CHR rules (:doc:`../features/constraints-syntax`).


Example
=======

.. elpi:: ../code/rules.elpi
   :assert: alice has 2 descendants
