#############################
File structure and attributes
#############################

A program is one or more files, each a sequence of rules, signatures
(:doc:`type-declarations`) and directives. What follows are the directives
that stitch files together and organise names, and how they combine into a
multi-file program. The attributes that decorate individual rules (``:name``,
``:if``, ``:untyped`` and the rest) are described in :doc:`rule-attributes`.


Accumulating files
==================

``accumulate`` loads another file:

.. code-block:: elpi

   accumulate stdlib.            % loads stdlib.elpi
   accumulate parser, printer.   % several at once
   accumulate "lib/json".        % a quoted path, for names with . or /

The ``.elpi`` extension is added automatically. A plain name is resolved first
relative to the file that accumulates it, and then along every directory
passed with ``elpi -I PATH`` (repeatable); this is how a program accumulates
an installed library by name without knowing where it sits on disk. A file is
loaded **once** even if it is accumulated from several places, so accumulation
forms a graph, not a tree.

``import`` and ``accum_sig`` load Teyjus ``.mod`` / ``.sig`` files and are
covered in :doc:`../compatibility`.


Namespaces
==========

``namespace n { … }`` prefixes every name **defined** inside the block with
``n.``:

.. code-block:: elpi

   namespace json {
     func parse string -> term.
     parse S T :- tokenize S Ts, parse-tokens Ts T.
   }

   main :- json.parse Text T.

A name only *used* inside the block, not defined there, stays global.

``namespace`` blocks nest, and so do their prefixes: a predicate declared in
``namespace outer { namespace inner { … } }`` is reached from outside as
``outer.inner.name``.

A leading ``.`` on a name escapes back to the global scope, which is how code
inside a namespace reaches a name it has itself shadowed (see
:doc:`lexical-conventions`):

.. elpi:: ../code/namespaces.elpi
   :assert: \*hi\* \*hi\*!

Shortening names
================

``shorten`` introduces a local alias for a qualified name:

.. code-block:: elpi

   shorten std.{ map, rev }.          % write `map` for `std.map`
   shorten std.{ list.map, string.{ concat, escape } }.   % a trie of names

The part before ``{`` is dropped, what is inside is kept: the second line makes
``list.map``, ``string.concat`` and ``string.escape`` stand for the
corresponding ``std.…`` names. A ``shorten`` is in effect until the end of the
file or of the enclosing ``{ … }`` block.


A library's public surface
==========================

Namespacing and ``shorten`` together let a file expose a small public API and
keep its helpers out of the way: nest the helpers under an ``internal``
namespace, define the public predicates alongside it (they reach
``internal.…`` unqualified, being in the same enclosing namespace), and
``shorten`` only the public names for whoever accumulates the file.

.. elpi:: ../code/library-api.elpi
   :assert: result: 21


Macros
======

``macro @name Args :- Body.`` defines a macro, expanded at compile time. Macro
names start with ``@`` (:doc:`lexical-conventions`). A macro is not a
predicate: it disappears before the program runs, and it does not cross a file
or block boundary, being visible only in the file (or ``{ … }`` block) that
defines it.

.. code-block:: elpi

   macro @newline :- "\n".
   macro @of X N T :- (of X T, pp X N).

Expansion is *hygienic*: a macro's own variables, those in ``Body`` not among
``Args``, get a fresh instance at every expansion, distinct from anything at
the use site, even a variable spelled the same way. Writing a macro is
therefore as safe as writing a predicate with its own local variables, with no
need to pick unlikely names to avoid a clash.

.. elpi:: ../code/macro-hygiene.elpi
   :assert: macro's Tmp = 5\ncaller's Tmp is still 999

A macro is a natural way to name a recurring combination of goals. ``@of``
above pairs the "typed" and "pretty-printed" facts that a hypothetical rule
(:doc:`inference-rules-and-queries`) must add together at every bound variable
of a term with binders; each ``@of x Name A`` expands to ``of x A, pp x Name``
in place, so the two cannot drift apart as the surrounding code changes:

.. code-block:: elpi

   of (lambda Name F) (arr A B) :-
     pi x\ @of x Name A ==> of (F x) B.


A multi-file program
====================

A library file, its predicate under a ``table`` namespace:

.. literalinclude:: ../code/table-lib.elpi
   :language: elpi

and a program that accumulates it, ``shorten``\ s the namespaced name, defines
a macro, and grafts a rule before a named fallback:

.. elpi:: ../code/file-structure.elpi
   :assert: two = 2 / nope = 0
