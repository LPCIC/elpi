#############################
File structure and attributes
#############################

.. note::

   **Stub — part of the manual outline.**

   Planned content: how a program is split across files and how its rules and
   signatures are decorated with attributes.

   The file model: ``accumulate`` (each file is loaded once; relative paths and
   quoted string paths). ``namespace { … }`` prefixing. ``shorten`` (including
   the trie syntax) and its scope. ``macro @name Args :- Body.`` — hygienic,
   compile-time expansion. ``constraint`` / ``rule`` blocks — their syntax is
   in *Constraint handling rules*.

   The rule-attribute catalogue, written ``:``-prefixed before a rule:
   ``:name``, ``:before``, ``:after``, ``:replace``, ``:remove`` (grafting),
   ``:if`` (conditional compilation) and ``:untyped`` (skip type checking for
   that rule). The lexer-level ``% elpi:if`` / ``% elpi:endif`` /
   ``% elpi:skip`` directives.

   Source material: ELPI.md; src/builtin.elpi.

   Examples will live in external ``.elpi`` files under ``docs/base/code/`` and
   be injected with the ``.. elpi::`` directive plus an ``:assert:`` line
   pinning the printed output.
