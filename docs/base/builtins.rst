###################
Built-in predicates
###################

Every predicate not written in Elpi itself — implemented in OCaml through the
FFI (:doc:`embedding`) — is a **builtin**. ``elpi -document-builtins`` prints
the exhaustive, generated reference, one signature and doc comment per
predicate (the very same listing is checked into the repository as
``src/builtin.elpi``); this chapter is a guided tour by category, with the
handful already covered in depth elsewhere cross-referenced rather than
repeated.


Logic, control and inspection
================================

``=`` unifies, with the occur check; ``unsound_unif`` does the same *without*
it and so can build a cyclic term (:doc:`compatibility`, where it is defined
with ``:nooc``). ``same_term`` — infix ``==`` — tests plain syntactic
equality, assigning nothing. ``pattern_match T P`` matches ``T`` against the
pattern ``P``, assigning only ``P``'s variables
(:doc:`syntax/terms`).

``declare_constraint`` and ``print_constraints`` are
:doc:`syntax/constraint-handling-rules`.

The cut ``!``, ``not``, ``if``/``if2``, ``halt``/``stop``, ``std.once`` and
``std.do!`` are :doc:`features/control-and-cut`; ``pi``/``sigma`` are
:doc:`syntax/inference-rules-and-queries`.

``ground_term T`` checks that ``T`` has no unification variables left;
``closed_term`` yields a fresh variable barred from naming any eigenvariable
(:doc:`features/binders-and-hoas`); ``cmp_term`` orders two terms
structurally, and only works when both are ground.

``name``/``names`` list the eigenvariables in scope, ``var`` recognises and
takes apart a unification variable (:doc:`features/unification-and-variables`
for its ``uvar Hd Args`` form), ``constant`` a global constant, and
``occurs A T`` checks whether the atom ``A`` appears in ``T`` —
:doc:`features/unification-and-variables`.

``new_int`` hands out a strictly increasing integer and ``new_safe`` a store
that survives backtracking; both step outside Elpi's usual scoping, so use
them sparingly.


Arithmetic
============

``X is Expr`` evaluates ``Expr`` and unifies the result with ``X``; ``calc``
is the same as a function, handy with spilling (:doc:`features/spilling`):
``f {calc (N + 1)}``. The precedences of every operator below are in
:doc:`syntax/lexical-conventions`.

Evaluated inside ``is`` / ``calc``:

* **binary** ``+`` ``-`` ``*`` (``int`` or ``float``), ``/`` (``float``),
  ``div`` ``mod`` (``int``), ``^`` (``string`` concatenation);
* **unary** ``~`` (negation), ``abs``, and, for ``float``, ``sqrt`` ``sin``
  ``cos`` ``arctan`` ``ln``;
* **two-argument functions** ``min`` ``max``;
* **conversions** ``int_to_real`` ``truncate`` ``floor`` ``ceil``
  (``int`` ↔ ``float``), ``int_to_string`` ``string_to_int``
  ``real_to_string`` ``substring`` ``size`` (``string``), ``chr`` ``rhc``
  (``int`` ↔ one-character ``string``);
* type-suffixed variants that fix the operand type instead of inferring it:
  ``i+ i- i* i~ iabs`` for ``int``, ``r+ r- r* r~ rabs`` for ``float``.

Comparisons are *goals*, not expressions — ``X < Y`` succeeds or fails, it is
not written under ``is``: ``<`` ``>`` ``=<`` ``>=`` work on ``int``,
``float`` or ``string``, with ``i< r< s<`` … fixing the type.

This set is **extensible from the host application**: ``API.Calc.register``
adds an operation (a symbol, its argument types, and an OCaml function) to a
``calc_descriptor`` passed to ``API.Setup.init ~calc`` — see :doc:`embedding`.


Standard data types
======================

These are declared in the builtin library, ready to use without an
``accumulate``:

.. code-block:: elpi

   data bool.        symb tt bool.  symb ff bool.
   data pair A B.    symb pr A -> B -> pair A B.            % + func fst, func snd
   data option A.    symb none option A.  symb some A -> option A.
   data cmp.         symb eq cmp.  symb lt cmp.  symb gt cmp.
   data diagnostic.  symb ok diagnostic.  symb error string -> diagnostic.
   data triple A B C.  symb triple A -> B -> C -> triple A B C.  % + triple_1..3

``bool`` uses ``tt``/``ff`` because ``true``/``false`` are goals; ``pair``'s
constructor is ``pr`` because ``,`` is conjunction; ``cmp`` is the result of a
three-way comparison (``cmp_term``, ``std.compare``); ``diagnostic`` is
returned by builtins that report a *reason* for failing rather than just
failing (``ok`` / ``error "message"``). ``list`` (``::`` / ``[]``) is built
in too — :doc:`syntax/terms`.


I/O and the file system
==========================

``print`` and ``dprint`` write their arguments (human-readable, respectively
debug-oriented) to standard output; ``term_to_string`` renders a term to a
``string`` instead of printing it. Opening, reading, writing and closing
files and standard streams, and querying the file system (``sys.file_exists``
and friends — the running example of :doc:`embedding`), are all builtins too;
see ``elpi -document-builtins`` for the full signatures.


Regular expressions and randomness
=====================================

``rex.match``, ``rex.replace`` and ``rex.split`` (OCaml's ``Str`` syntax, not
PCRE) cover the common text-processing needs. ``random.int N`` draws a
uniform integer in :math:`[0, N)`; ``random.init Seed`` reseeds the
generator, making a sequence reproducible — the same seed always draws the
same numbers, as the Example below shows.


Example
=======

.. elpi:: code/builtins-tour.elpi
   :assert: calc: 14\nterm_to_string: pr 1 one\nrex.split: \[a, b, c\]\nseeded random repeats: (\d+) \1
