###################
Built-in predicates
###################

A **builtin** is a predicate whose body is OCaml rather than Elpi, reached
through the foreign function interface (:doc:`embedding`). Elpi's own library
ships close to two hundred of them, from ``=`` to the garbage-collector
controls; a host application registers more the same way.

The FFI fixes the shape a builtin can have. Each argument is declared *input*
or *output* and carries a *conversion* between an Elpi term and an OCaml
value, so the OCaml code receives its inputs already converted and hands back
its outputs to be converted on the way out. A builtin succeeds once or fails
(by raising ``No_clause``); it does not backtrack and does not offer a second
solution on its own, so one that needs to enumerate returns a list. A term it
has no conversion for it can still carry through untouched, as ``any``.

``elpi -document-builtins`` prints the exhaustive, generated reference: one
signature and doc comment per predicate, the same text checked in as
``src/builtin.elpi``. What follows is a tour by category, saying what each
group is for and which chapter covers it in depth where one does.


Logic, control and inspection
=============================

``=`` unifies, with the occur check; ``unsound_unif`` does the same *without*
it and so can build a cyclic term (:doc:`features/unification-and-variables`,
where it is defined with ``:nooc``). ``same_term``, infix ``==``, tests
plain syntactic equality, assigning nothing. ``pattern_match T P`` matches
``T`` against the pattern ``P``, assigning only ``P``'s variables
(:doc:`syntax/terms`).

``declare_constraint`` and ``print_constraints`` are covered in
:doc:`syntax/constraint-handling-rules`.

The cut ``!``, ``not``, ``if`` / ``if2``, ``halt`` / ``stop``, ``std.once``
and ``std.do!`` are covered in :doc:`features/control-and-cut`, and
``pi`` / ``sigma`` in :doc:`syntax/inference-rules-and-queries`.

``ground_term T`` checks that ``T`` has no unification variables left;
``closed_term`` yields a fresh variable barred from naming any eigenvariable
(:doc:`features/binders-and-hoas`); ``cmp_term`` orders two terms
structurally, and only works when both are ground.

``name`` / ``names`` list the eigenvariables in scope, ``var`` recognises and
takes apart a unification variable (:doc:`features/unification-and-variables`
for its ``uvar Hd Args`` form), ``constant`` a global constant, and
``occurs A T`` checks whether the atom ``A`` appears in ``T``
(:doc:`features/unification-and-variables`).

``new_int`` hands out a strictly increasing integer and ``new_safe`` a store
that survives backtracking; both step outside Elpi's usual scoping, so use
them sparingly.


Arithmetic
==========

``X is Expr`` evaluates ``Expr`` and unifies the result with ``X``; ``calc``
is the same as a function, for use with spilling (:doc:`features/spilling`):
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

Comparisons are *goals*, not expressions: ``X < Y`` succeeds or fails, it is
not written under ``is``. ``<`` ``>`` ``=<`` ``>=`` work on ``int``,
``float`` or ``string``, with ``i< r< s<`` … fixing the type.

This set is **extensible from the host application**: ``API.Calc.register``
adds an operation (a symbol, its argument types, and an OCaml function) to a
``calc_descriptor`` passed to ``API.Setup.init ~calc`` (:doc:`embedding`).


Standard data types
===================

These are declared in the builtin library, ready to use without an
``accumulate``:

.. code-block:: elpi

   data bool.
   symb tt bool.
   symb ff bool.

   data pair A B.
   symb pr A -> B -> pair A B.       % + func fst, func snd

   data option A.
   symb none option A.
   symb some A -> option A.

   data cmp.
   symb eq cmp.
   symb lt cmp.
   symb gt cmp.

   data diagnostic.
   symb ok diagnostic.
   symb error string -> diagnostic.

   data triple A B C.
   symb triple A -> B -> C -> triple A B C.   % + triple_1..3

``bool`` uses ``tt`` / ``ff`` because ``true`` / ``false`` are goals; ``pair``'s
constructor is ``pr`` because ``,`` is conjunction; ``cmp`` is the result of a
three-way comparison (``cmp_term``, ``std.compare``); ``diagnostic`` is
returned by builtins that report a *reason* for failing rather than just
failing (``ok`` / ``error "message"``). ``list`` (``::`` / ``[]``) is built
in too (:doc:`syntax/terms`).

A short tour of ``calc``, a ``pair``, ``term_to_string``, ``rex.split`` and a
reseeded generator:

.. elpi:: code/builtins-tour.elpi
   :assert: calc: 14\nterm_to_string: pr 1 one\nrex.split: \[a, b, c\]\nseeded random repeats: (\d+) \1


Regular expressions and randomness
==================================

``rex.match``, ``rex.replace`` and ``rex.split`` (OCaml's ``Str`` syntax, not
PCRE) cover the common text-processing needs. ``random.int N`` draws a
uniform integer in :math:`[0, N)`; ``random.init Seed`` reseeds the
generator, making a sequence reproducible: the same seed always draws the
same numbers.


Input, output and the file system
=================================

``print`` and ``dprint`` write their arguments to standard output (``dprint``
shows raw terms); ``term_to_string`` renders a term to a ``string`` instead of
printing it. Beyond that Elpi has the stream I/O of a small scripting
language:

* ``open_in`` / ``open_out`` / ``open_append`` open a file; ``open_string``
  turns a string into a readable stream; ``std_in`` / ``std_out`` /
  ``std_err`` are the standard streams;
* ``input InStream Bytes S`` reads a fixed number of bytes, ``input_line``
  reads up to the newline, ``lookahead`` peeks one byte, ``eof`` tests for
  end of input;
* ``output OutStream S`` writes, ``flush`` forces pending output out,
  ``close_in`` / ``close_out`` close.

``sys.*`` reaches the file system and the process environment:
``sys.file_exists``, ``sys.is_directory``, ``sys.mkdir`` / ``sys.rmdir``,
``sys.remove`` / ``sys.rename``, ``sys.readdir``, ``sys.chdir`` /
``sys.getcwd``, plus ``getenv``, ``gettimeofday`` and ``system`` (run a shell
command). The calls that can fail for an external reason return a
``diagnostic`` (``ok`` or ``error "…"``) rather than just failing.
``unix.process.open`` / ``unix.process.close`` spawn a subprocess and reap
it, handing back its three standard streams.

.. elpi:: code/builtins-io.elpi
   :assert: first two lines: alpha beta\nstring map, two -> 2


Typed finite maps
=================

``std.string.map``, ``std.int.map`` and ``std.loc.map`` are FFI-backed
persistent maps over one fixed key type (``std.string.set`` and
``std.int.set`` are the matching sets). Each map has ``.empty``, ``.mem``,
``.add``, ``.remove``, ``.find`` and ``.bindings``, plus ``.filter`` /
``.map`` / ``.fold`` taking an Elpi ``func``; the value type has to be a
closed term. The general, any-key structures ``std.map`` and ``std.set``,
written in Elpi rather than OCaml, are covered in :doc:`standard-library`.


Garbage collector and runtime
=============================

``gc.get`` / ``gc.set`` read and write the OCaml garbage-collector
parameters, ``gc.stat`` / ``gc.quick-stat`` report live statistics, and
``gc.minor`` / ``gc.major`` / ``gc.full`` / ``gc.compact`` force a
collection. ``trace.counter`` reads a named trace point
(:doc:`debugging-and-tracing`). These matter only when profiling or trimming
the footprint of a long-running embedding.
