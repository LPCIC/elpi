####################
The standard library
####################

The ``std.`` namespace (:doc:`syntax/file-structure-and-attributes`) gathers
list and option combinators, associative structures, and a few
overridable hooks. It is written in Elpi, and its full signatures are printed
by ``elpi -document-builtins`` (or read straight from |stdlib_file|). What
those signatures do not tell you is what follows: the naming conventions,
and which structure to reach for.


Naming conventions
==================

A suffix on a combinator's name says how it varies from the plain form:

* ``!``: a cut is baked in, so the call commits to its first solution.
  :stdlib:`std.mem!` beside the backtracking :stdlib:`std.mem`, :stdlib:`std.lookup!`
  beside :stdlib:`std.lookup`.
* ``2``: walks two lists in lockstep, raising a fatal error if their lengths
  differ. :stdlib:`std.map2`, :stdlib:`std.fold2`, :stdlib:`std.forall2`, :stdlib:`std.exists2`.
* ``-i``: the callback also receives the element's 0-based index.
  :stdlib:`std.map-i`, :stdlib:`std.list.init`.
* ``-filter``: the callback may fail, and where it does the element is
  dropped. :stdlib:`std.map-filter` is map and filter in one pass.
* ``-ok``: the callback's last output is a ``diagnostic``; the first
  ``error`` stops the traversal and is returned. :stdlib:`std.map-ok`,
  :stdlib:`std.forall-ok`, :stdlib:`std.while-ok-do!`.
* ``R``: a *relation*, with every argument output-mode, so the predicate runs
  in any direction. Only one predicate has it,
  :stdlib:`std.appendR`: ``std.appendR X Y [1,2,3]`` enumerates every way to
  split the list, not only the one where ``X`` and ``Y`` are already known.

Two hooks are ordinary named rules (:doc:`syntax/rule-attributes`) that a
program can graft over to change how the library behaves. Every error the
library raises goes through :stdlib:`std.fatal-error` / :stdlib:`std.fatal-error-w-data`,
and every debug line through :stdlib:`std.debug-print`; grafting a rule
``:before "default-fatal-error"`` turns a library error into something the
host catches instead of a ``halt``.


List and option combinators
===========================

:stdlib:`std.map`, :stdlib:`std.filter`, :stdlib:`std.fold`, :stdlib:`std.exists`, :stdlib:`std.forall`,
:stdlib:`std.mem`, :stdlib:`std.append`, :stdlib:`std.rev`, :stdlib:`std.length`, :stdlib:`std.nth`,
:stdlib:`std.take` / :stdlib:`std.drop`, :stdlib:`std.zip` / :stdlib:`std.unzip`, :stdlib:`std.iota` and
their relatives mirror what a functional language's list module offers; the
suffix conventions above generate the rest of the family from each base name.
:stdlib:`std.omap` is the ``option`` counterpart of :stdlib:`std.map`.

.. elpi:: code/stdlib-tour.elpi
   :assert: map-i \(index added\): \[10, 21, 32\]\nmap-filter \(evens kept\): \[2, 4\]\nfold2 \(dot product\): 140\nstd.map, x -> 1\nappendR split: \[\] \[1, 2\]\nappendR split: \[1\] \[2\]\nappendR split: \[1, 2\] \[\]


Associative structures
======================

Four map/set families, differing in what keys they take and how they are
implemented:

* ``std.map`` and ``std.set`` take any key type, given a comparator
  ``func K, K -> cmp`` passed to ``.make``. They are balanced search trees
  written in Elpi, so a key may contain unification variables.
* ``std.fmap`` and ``std.fset`` are the same trees, but skip the occur check
  for a speed gain. They require every key to be a *ground* term and raise a
  fatal error otherwise.
* ``std.string.map``, ``std.int.map``, ``std.loc.map`` (and
  ``std.string.set`` / ``std.int.set``) are the FFI-backed structures for one
  fixed key type, backed by OCaml's own maps (:doc:`builtins`).

``std.map`` shares its name with the list-mapping combinator; a predicate and
a type live in different namespaces, so this is unambiguous but easy to
misread.
