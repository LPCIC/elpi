####################
The standard library
####################

``accumulate std.`` — or nothing: most programs pull it in transitively — puts
the ``std.`` namespace (:doc:`features/program-organization`) in scope: list
and option combinators, associative structures, and a handful of hooks. Full
signatures are ``elpi -document-builtins`` / ``src/builtin.elpi`` /
``src/builtin_stdlib.elpi``, alongside the plain builtins
(:doc:`builtins`); this chapter is its conventions and shape.


Naming conventions
=====================

A name ending in ``R`` is a relation: every argument is output-mode, so it
can be used to *generate* as well as check — ``std.appendR X Y [1,2,3]``
enumerates every way to split the list, not just the one where ``X`` and
``Y`` are already known (see the Example below). A name ending in ``!``
commits to the first solution — a cut baked in, like ``std.mem!`` next to the
plain, backtracking ``std.mem``. Every error the library itself raises goes
through ``std.fatal-error`` / ``std.fatal-error-w-data``, and every debug
message through ``std.debug-print`` — both named rules
(:doc:`features/rule-grafting`) a program can override to change how the
library reports problems, without touching the library itself.


List and option combinators
==============================

``std.map``, ``std.filter``, ``std.fold``, ``std.exists``, ``std.forall``,
``std.mem``, ``std.append``, ``std.rev``, ``std.length``, ``std.nth``, and
their friends, cover the usual traversal and construction patterns over
``list`` and ``option`` — a mirror of what a functional language's standard
list module offers, discoverable in full via ``-document-builtins``.


Associative structures
==========================

``std.string.map``, ``std.int.map`` and ``std.loc.map`` (and the matching
``…\ .set``) are fast, FFI-backed structures for one specific key type.
``std.map`` — confusingly sharing its name with the list-mapping predicate
above, since a predicate and a type live in different namespaces — and
``std.set`` are the general case: given a comparator (``func K, K -> cmp``),
they work over any key type, implemented as an Elpi search tree rather than
in OCaml. ``std.fmap``/``std.fset`` are the same, faster, for ground terms
only, trading away the occur check.


Example
=======

.. elpi:: code/stdlib-tour.elpi
   :assert: std.map \(list\): \[1, 4, 9\]\nstd.string.map.find b: 2\nstd.mem! finds the first 1: yes\nappendR generated: \[\] \[1, 2, 3\]\nappendR generated: \[1\] \[2, 3\]\nappendR generated: \[1, 2\] \[3\]\nappendR generated: \[1, 2, 3\] \[\]
