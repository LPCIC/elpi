###################
Lexical conventions
###################

An Elpi source file is UTF-8 text. It is a sequence of *clauses* and
*directives*, each terminated by a full stop ``.``. Whitespace — spaces, tabs,
carriage returns and newlines — separates tokens and is otherwise insignificant;
the terminating ``.`` does not need to sit on a line of its own.

This chapter describes how the text is broken into tokens. The grammar that
assembles those tokens into terms and clauses is covered in
:doc:`terms-and-operators` and :doc:`clauses-and-queries`.


Comments
========

.. code-block:: elpi

   % a line comment runs to the end of the line

   /* a block comment,
      /* which may be nested */
      up to the matching close */

Block comments nest, so commenting out a region that already contains a
``/* … */`` works as expected.

Line comments that start with ``% elpi:`` are directives to the lexer rather
than ordinary comments (``% elpi:skip``, ``% elpi:if`` / ``% elpi:endif``); see
:doc:`../features/conditional-compilation`.


Names
=====

A name (an identifier) starts with a letter, ``_`` or ``@``, and continues with
any number of letters, digits, ``_``, ``-``, ``$`` and the *symbol characters*

.. code-block:: text

   +  *  /  ^  <  >  `  '  ?  @  #  ~  =  &  !

(a run made only of symbol characters is instead read as an operator — see
`Operators`_ below).

The **first character decides the role of the name**:

* a name starting with an **uppercase letter** is a **unification variable** —
  ``X``, ``Acc``, ``Result1`` (a name starting with ``_`` is also variable-like,
  but a *wildcard* — see below);
* every other name is a **constant** — a predicate or a term constructor:
  ``append``, ``red``, ``std.length``, ``make-palindrome``, ``@of``.

.. code-block:: elpi

   copy (app A B) (app C D) :- copy A C, copy B D.
   %    ^^^ ^ ^   constructors (lowercase)      ^ variables (uppercase)

A name may not *start* with ``-`` or a digit, but it may *contain* them: a
lowercase-initial name like ``make-palindrome`` or ``v1`` is a single token.
Write ``X - Y`` (with spaces) for subtraction. A name may start with ``@``, and
macros conventionally do.

.. rubric:: Qualified names

A ``.`` immediately followed by a letter is part of the name: ``std.list.map``
is a single constant, not ``std`` applied to ``list.map``. This is what
:doc:`../features/program-organization` uses for namespaces. A ``.`` *not*
followed by a letter is the clause terminator.

.. rubric:: The wildcard

A bare ``_`` is a fresh anonymous variable. A name that *starts* with ``_``
(``_x``, ``_Acc``) is also a wildcard — never a variable that can be referred
to again. See :doc:`../features/unification-and-variables`.

.. rubric:: Quoted names

A name may be wrapped in back-quotes or single quotes so that a symbol which is
normally an operator can be used as a plain constant; the quotes are part of the
name, and the wrapped text may only contain letters, digits and symbol
characters (no spaces, no ``.``).

.. code-block:: elpi

   X = `->`,     % one constant whose name is:  `->`
   Y = 'eq'.     % one constant whose name is:  'eq'

These forms pair with the back-quote and single-quote quotations of the OCaml
API.


Literals
========

.. rubric:: Integers

A run of digits, optionally with a leading ``-`` **and no space in between**:
``0``, ``42``, ``-2``. With a space, ``- 2`` and ``~ 2`` are the unary minus
applied to ``2``. There is no ``0x`` / ``0o`` / ``0b`` notation and no digit
separators (``1_000`` is not a number).

.. rubric:: Floating point

A digit sequence, a ``.``, and a digit sequence: ``3.0``, ``-1.5``; a leading
``.`` is allowed (``.5``). Note that ``3.`` is the integer ``3`` followed by the
clause terminator. There is no exponent notation.

.. rubric:: Strings

Delimited by ``"``. A string literal may span several lines. The escapes
``\n``, ``\t``, ``\b``, ``\r``, ``\\`` and ``\"`` are recognised, and a doubled
``""`` stands for one ``"``. There are no octal or hexadecimal escapes.

.. code-block:: elpi

   Msg = "he said ""hi"" and\nleft"


Operators
=========

Elpi has a fixed set of built-in mixfix operators (``,``  ``;``  ``=>``  ``:-``
``::``  ``+``  ``*``  ``is`` …). Each belongs to a *family* identified by its
leading character(s), and the family fixes its precedence and associativity;
there is no ``infix`` / ``prefix`` directive to declare new ones. The full table
is in :doc:`../operators-and-grammar`.


Keywords
========

The following words are reserved and cannot be used as names: the declaration
introducers ``kind``, ``type``, ``typeabbrev``, ``pred``, ``func``,
``external``, ``symbol``, ``macro``, ``namespace``, ``shorten``,
``accumulate``, ``constraint``, ``rule``, and the binders ``pi``, ``sigma`` and
``as``. Immediately after a ``:``, the words ``before``, ``after``,
``replace``, ``remove``, ``name``, ``if``, ``index``, ``functional``,
``untyped`` and ``nooc`` introduce clause and rule attributes.


The token grammar
=================

The character classes named above are, verbatim, the ones the ``ocamllex``
lexer uses:

.. literalinclude:: ../../../src/parser/lexer.mll.in
   :language: ocaml
   :start-at: let digit =
   :end-at: let symbcharplus

``num`` is an integer; ``num "." pnum`` or ``"." pnum`` is a float. A name comes
from exactly one of these productions (the keyword rules in between are elided):

.. code-block:: ocaml

   | "_" idchar+            { CONSTANT }   (* _foo, _Acc : a wildcard   *)
   | "_"                    { FRESHUV  }   (* the anonymous variable    *)
   | ucase idcharstar       { CONSTANT }   (* X, Foo1, X+Y : a variable *)
   | lcase idcharstarns     { CONSTANT }   (* foo, std.rev, x+y         *)
   | "." idcharstarns       { CONSTANT }   (* .aux : a qualified tail   *)
   | '@' idcharstar         { CONSTANT }   (* @macro                    *)
   | '\'' symbcharstar '\'' { CONSTANT }   (* 'eq'                      *)
   | '`'  symbcharstar '`'  { CONSTANT }   (* `->`                      *)

``idcharstarns`` is ``idcharstar`` extended with an embedded ``.`` before a
letter — that is what makes ``std.rev`` a single token. All eight productions
emit the same ``CONSTANT`` token; the compiler decides *variable vs constant*
afterwards, from the first character.


Relation to Teyjus
==================

Elpi's tokens are close to those of `Teyjus
<https://github.com/teyjus/teyjus/wiki/TeyjusTokens>`_. Both share the same
identifier character set (letters, digits and the sign characters ``+ - * / ^
< > = ` ' ? @ # $ & ! _ ~``), the same rule for telling a variable from a
constant (a leading ``_`` or upper-case letter marks a variable), the same
integer and real shapes (``.5`` yes, ``3.`` no), and the same comments (``%``
to end of line, nesting ``/* */``). They differ in:

* **Name start.** A Teyjus name may start with a sign character (``=abc`` is one
  name). An Elpi name must start with a letter, ``_``, ``@`` or ``.``; a leading
  sign character begins an operator.
* **Dot.** ``.`` is punctuation in Teyjus. In Elpi ``.`` before a letter
  continues a qualified name.
* **Negative numbers.** ``-2`` (no space) is an integer literal in Elpi; Teyjus
  has no negative numeric literal.
* **Strings.** An Elpi string may contain a literal newline; a Teyjus string may
  not. Teyjus recognises many more escapes (``\a \v \f \e \d \^c \ddd \xhh`` …);
  Elpi recognises ``\n \b \t \r \\ \"`` and the doubled ``""``.
* **Empty list.** ``[]`` in Elpi, ``nil`` in Teyjus.
* **Operators.** Teyjus programs declare operators with ``infix`` / ``prefix`` /
  … ; Elpi's operator set is fixed (:doc:`../operators-and-grammar`).


Example
=======

.. elpi:: ../code/lexical.elpi
   :assert: items: 2 discount: -5
