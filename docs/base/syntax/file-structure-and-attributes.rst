#############################
File structure and attributes
#############################

A program is one or more files, each a sequence of rules, signatures
(:doc:`type-declarations`) and directives. This chapter covers the directives
that stitch files together and organise names, and the attributes that decorate
individual rules. How scoping actually resolves is
:doc:`../features/program-organization`.


Accumulating files
==================

``accumulate`` loads another file:

.. code-block:: elpi

   accumulate stdlib.            % loads stdlib.elpi
   accumulate parser, printer.   % several at once
   accumulate "lib/json".        % a quoted path, for names with . or /

The ``.elpi`` extension is added automatically; a plain name is resolved
relative to the file that accumulates it (and then along the ``-I`` search
path). A file is loaded **once** even if it is accumulated from several places,
so accumulation forms a graph, not a tree.

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


Macros
======

``macro @name Args :- Body.`` defines a macro, expanded at compile time. Macro
names start with ``@`` (:doc:`lexical-conventions`); expansion is hygienic.

.. code-block:: elpi

   macro @newline :- "\n".
   macro @of X N T :- (of X T, pp X N).

A macro is not a predicate: it disappears before the program runs. Currently a
macro does not cross a file or block boundary — it is visible only in the file
(or ``{ … }`` block) that defines it.

Rule attributes
===============

An attribute is written ``:``-prefixed before a rule — a fact or a
``head :- body`` — and may sit on its own line; several may be stacked.

.. code-block:: elpi

   :name "step" :if "DEBUG"
   step X :- ...

* ``:name "N"`` names the rule, for grafting and for trace output.
* ``:before "N"`` / ``:after "N"`` insert the rule immediately before / after
  the rule named ``N`` instead of at the end of the predicate's rules.
* ``:replace "N"`` / ``:remove "N"`` swap out / delete the rule named ``N``.
  They only apply to a rule of the *same* predicate, and the new rule may not
  itself carry ``:name``. See :doc:`../features/rule-grafting`.
* ``:if "V"`` keeps the rule only when the compiler variable ``V`` is defined
  (``elpi -D V``); it also works on CHR rules. See
  :doc:`../features/conditional-compilation`.
* ``:untyped`` turns the type checker off for that one rule.

Attributes that describe a *predicate* — ``:index``, ``:functional``,
``:external`` — go on its ``pred`` / ``func`` signature instead
(:doc:`type-declarations`).


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
See :doc:`../features/conditional-compilation`.


Example
=======

The accumulated library:

.. literalinclude:: ../code/table-lib.elpi
   :language: elpi

.. elpi:: ../code/file-structure.elpi
   :assert: two = 2 / nope = 0
