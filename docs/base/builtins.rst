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


Logic and control
====================

``=`` unifies; ``pi``/``sigma``/``pattern_match`` and the cut ``!`` are
:doc:`syntax/terms-and-operators`, :doc:`syntax/inference-rules-and-queries`,
:doc:`features/control-and-cut` — which also covers ``not``, ``if``/``if2``,
``halt``/``stop``, ``std.once`` and ``std.do!``. ``declare_constraint`` and
``print_constraints`` are :doc:`syntax/constraint-handling-rules`.


Arithmetic
============

``X is Expr`` evaluates ``Expr`` and unifies the result with ``X``; ``calc``
is the same as a function, handy with spilling (:doc:`features/spilling`):
``f {calc (N + 1)}``. The arithmetic and comparison operators themselves —
``+``, ``-``, ``<``, the type-specific ``i+``/``r+``/``s+`` families, and so
on — are listed in full in :doc:`syntax/lexical-conventions`.


Standard data types
======================

``bool`` (``tt``/``ff`` — not ``true``/``false``, which are goals), ``pair``
(constructor ``pr``, since ``,`` means conjunction), ``option``
(``some``/``none``), ``triple``, ``cmp`` (``eq``/``lt``/``gt``, the result of
a three-way comparison) and ``diagnostic`` (``ok``/``error S``, used by
builtins that report a reason for failure rather than just failing) are all
declared in the builtin library, ready to use without an ``accumulate``.


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


Non-logical inspection
=========================

``var``, ``name``/``names``, ``constant``, ``occurs`` and ``closed_term`` are
:doc:`features/unification-and-variables` and
:doc:`features/binders-and-hoas`. ``same_term`` and ``cmp_term`` compare two
terms without unifying them (structural / syntactic equality and ordering,
rather than unifiability); ``new_int`` and ``new_safe`` hand out fresh,
globally unique values outside of Elpi's usual scoping — an escape hatch, to
use sparingly.


Example
=======

.. elpi:: code/builtins-tour.elpi
   :assert: calc: 14\nterm_to_string: pr 1 one\nrex.split: \[a, b, c\]\nseeded random repeats: (\d+) \1
