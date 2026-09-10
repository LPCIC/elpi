###############
Rule attributes
###############

An attribute decorates a single rule (a fact or a ``head :- body``) with
information the compiler acts on before the program runs: where the rule sits
among its predicate's alternatives, whether it is kept at all, whether the
type checker inspects it. An attribute is written ``:``-prefixed before the
rule and may sit on its own line; several may be stacked.

.. code-block:: elpi

   :name "step" :if "DEBUG"
   step X :- ...

Attributes that describe a *predicate* rather than one of its rules
(``:index``, ``:functional``, ``:external``) go on the ``pred`` / ``func``
signature instead (:doc:`type-declarations`).


Grafting
========

Five attributes place a rule relative to the others of its predicate:

* ``:name "N"`` gives the rule a stable name, used for grafting and in trace
  output.
* ``:before "N"`` / ``:after "N"`` insert the rule immediately before or after
  the rule named ``N``, instead of at the end of the predicate's rules.
* ``:replace "N"`` / ``:remove "N"`` swap out or delete the rule named ``N``.

Grafting lets code accumulated later change what a library does without
touching the library file. The library gives a rule a stable name (a "fatal
error" or "default handler" rule is the usual candidate), and a client
accumulated afterwards grafts its own rule in front:

.. elpi:: ../code/grafting.elpi
   :assert: custom: hello

Once ``custom-report`` cuts, ``default-report`` is never tried for that call;
without the cut both would run on backtracking. ``:after`` inserts the other
way round.

``:replace`` and ``:remove`` act only on a rule of the *same* predicate.
Naming another predicate's rule is a hard error ("cannot remove a clause for
another predicate"), so a typo in the name string fails loudly instead of
doing nothing silently. The replacing or removed rule may not itself carry
``:name``: allowing it would make the outcome depend on the order in which two
files that both replace the same rule are accumulated.


Conditional compilation
=======================

A rule marked ``:if "NAME"`` is part of the program only when the compiler
variable ``NAME`` is defined; otherwise it is dropped as though never written,
with no trace at run time. ``elpi -D NAME`` (repeatable) defines one. The name
is an arbitrary string, not tied to any predicate. The typical use is a
debug-only rule, silent unless ``DEBUG`` is set:

.. code-block:: console

   $ elpi conditional.elpi -test -D DEBUG
   [debug] checkpoint 1
   done

.. elpi:: ../code/conditional.elpi
   :assert: done

``:if`` also works on CHR rules (:doc:`constraint-handling-rules`).


Suppressing the type checker
============================

``:untyped`` turns the type checker off for one rule. It is a last resort, for
a rule the checker cannot be taught to accept, usually one that builds terms
too dynamically for any signature to describe. Prefer fixing the signature, or
widening an argument to ``any`` (:doc:`type-declarations`); at a single spot,
the standard library's ``std.unsafe-cast`` (``func unsafe-cast A -> B``, itself
a ``:untyped`` rule) coerces one term without disarming the checker over the
whole rule. Reach for ``:untyped`` only when none of these works. An untyped
rule also loses the features that depend on type information: in particular
spilling (``{ … }``, :doc:`../features/spilling`) is not expanded inside it.


Lexer directives
================

Two directives are read by the lexer, before parsing, as ``%`` line comments:

.. code-block:: text

   % elpi:if version < 2.0.0
   text kept only for Elpi older than 2.0.0
   % elpi:endif

   % elpi:skip 2
   infixr ==> 120.       % two lines Elpi should ignore (e.g. Teyjus directives)
   infixr <== 120.

``% elpi:if`` takes a single ``version <component> <op> X.Y.Z`` test
(``<component>`` defaults to ``elpi``, ``<op>`` is one of ``< > = <= >=``) and
cannot be nested; ``% elpi:skip N`` drops the next ``N`` lines unconditionally.

The default ``elpi`` component is compared against Elpi's own version. Any
other component name is compared against a version the host registers through
``?versions`` on ``API.Setup.init`` (:doc:`../embedding`), a map from name to
a ``(major, minor, patch)`` triple; an unregistered name is a lexer error.
coq-elpi registers ``coq`` this way, so ``.elpi`` files it loads can guard on
the Rocq version with ``% elpi:if version coq >= X.Y.Z``.

Unlike ``:if``, these act on *text* rather than rules, which is what lets them
hide syntax Elpi itself does not accept, such as a directive meant for Teyjus
kept in a file the two interpreters share.
