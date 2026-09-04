###################
Lexical conventions
###################

An Elpi source file is read as a stream of bytes. It is a sequence of *rules*
and *directives*, each terminated by a full stop ``.``. Whitespace — spaces,
tabs, carriage returns and newlines — separates tokens and is otherwise
insignificant; the terminating ``.`` does not need to sit on a line of its own.

Outside string literals and comments only ASCII characters are used; a
non-ASCII byte there is a lexical error. Inside a string literal or a comment
any byte is accepted and passed through unchanged — so UTF-8 text can appear
there, but Elpi does not decode or validate it.

This chapter describes how the text is broken into tokens. The grammar that
assembles those tokens into terms and rules is covered in
:doc:`terms-and-operators` and :doc:`rules-and-queries`.


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


Identifiers
===========

An identifier starts with a letter or ``_``, and continues with any number of
letters, digits, ``_``, ``-``, ``$`` and the *symbol characters*

.. code-block:: text

   +  *  /  ^  <  >  `  '  ?  @  #  ~  =  &  !

(a run made only of symbol characters is instead read as an operator — see
`Operators`_ below).

The **first character decides the role of the name**:

* a name starting with an **uppercase letter** is a **unification variable** —
  ``X``, ``Acc``, ``Result1`` (a name starting with ``_`` is also variable-like,
  but a *wildcard* — see below);
* every other name is a **constant** — a predicate or a term constructor:
  ``append``, ``red``, ``std.length``, ``make-palindrome``.

.. code-block:: elpi

   copy (app A B) (app C D) :- copy A C, copy B D.
   %    ^^^ ^ ^   constructors (lowercase)      ^ variables (uppercase)

A name may not *start* with ``-`` or a digit, but it may *contain* them: a
lowercase-initial name like ``make-palindrome`` or ``v1`` is a single token.
Write ``X - Y`` (with spaces) for subtraction.

.. rubric:: Qualified names

A ``.`` immediately followed by a letter is part of the name: ``std.list.map``
is a single constant, not ``std`` applied to ``list.map``. This is what
:doc:`../features/program-organization` uses for namespaces. A ``.`` *not*
followed by a letter is the full stop that ends a rule or directive.

.. rubric:: The wildcard

A bare ``_`` is a fresh anonymous variable. A name that *starts* with ``_``
(``_x``, ``_Acc``) is also a wildcard — never a variable that can be referred
to again. See :doc:`../features/unification-and-variables`.

.. rubric:: Macro names

The character ``@`` is reserved to start macro names. A name that *begins*
with ``@`` always refers to a macro, which must have been defined with
``macro @name … :- ….`` — it can appear nowhere else. (``@`` anywhere other
than the first character is an ordinary name character.) See
:doc:`../features/macros`.


Literals
========

.. rubric:: Integers

A run of digits, optionally preceded by ``-`` with no space: ``0``, ``42``,
``-2``.

.. rubric:: Floating point

A digit sequence, a ``.``, and a digit sequence: ``3.0``, ``-1.5``; a leading
``.`` is allowed (``.5``). Note that ``3.`` is the integer ``3`` followed by the
full stop. There is no exponent notation.

.. rubric:: Strings

Delimited by ``"``. A string literal may span several lines. The escapes
``\n``, ``\t``, ``\b``, ``\r``, ``\\`` and ``\"`` are recognised, and a doubled
``""`` stands for one ``"``. There are no octal or hexadecimal escapes.

.. code-block:: elpi

   Msg = "he said ""hi"" and\nleft"

.. _quoted-identifiers:

.. rubric:: Quoted identifiers

A run of *identifier* characters — letters, digits, the symbol characters and
also ``:`` — enclosed in back-quotes or single quotes, with **no spaces**
inside. It is not a string, and on its own it is not a constant: it is an
identifier that the host application can choose to *compile* in a special way.
It looks like a string but can be given, for instance, case-insensitive
comparison. Quoting is also the only way to write an identifier that contains
``:`` or that begins with a symbol character.

.. code-block:: elpi

   X = `a:b`,        % one identifier (a bare name cannot contain ':')
   Y = 'CamelCase'.  % one identifier (a bare CamelCase would be a variable)

The compilation hooks are ``declare_backtick`` and ``declare_singlequote`` in
the ``Quotation`` module of ``src/API.mli``:

.. literalinclude:: ../../../src/API.mli
   :language: ocaml
   :start-at: (** Like quotations but for identifiers
   :end-before: val new_quotations_descriptor

With no hook registered, a quoted identifier is simply a constant with that
name.


Operators
=========

Operators are built in: there is no ``infix`` / ``prefix`` directive to declare
your own (Teyjus has one). An operator token is a run of symbol characters
(``,``, ``::``, ``=>``, ``+``, …); a few are ordinary words (``is``, ``div``,
``mod``).

.. rubric:: Token families

Precedence and associativity belong not to individual operators but to
**families**. A family is identified by its leading character(s): ``+-->``
belongs to the ``+`` family, ``*-->`` to the ``*`` family. Every token of a
family parses with the same precedence and associativity, and no declaration is
needed — ``x +--> y *--> z`` reads ``x +--> (y *--> z)`` because the ``*``
family binds tighter than the ``+`` family.

In the table below a family is written with a trailing ``..`` (``+..`` is "any
token starting with ``+``"); a bare entry is a *fixed* token, the sole member
of its family. A family marked ``[*]`` may not *end* with its starting
character — that is what lets ``` `foo` ``` and ``'foo'`` be read as
:ref:`quoted identifiers <quoted-identifiers>` rather than operators.

.. rubric:: Precedence, lowest to highest

.. code-block:: text

   fixity                     | tokens / token families
   -------------------------- + -----------------------------------
   Infix   not   associative  | :-   ?-
   Infix   right associative  | ;
   Infix   right associative  | ==>                              (1)
   Infix   right associative  | =!=>                             (1)
   Infix   right associative  | ,   &
   Infix   right associative  | ->
   Infix   right associative  | =>
   Infix   not   associative  | =  ==  =<  r<  i<  s<  r=<  i=<  s=<
                                <..  r>  i>  s>  r>=  i>=  s>=  >..  is
   Infix   right associative  | ::
   Infix   not   associative  | '..                             [*]
   Infix   left  associative  | ^..  r+  i+  s+  +..  -  r-  i-  s-
   Infix   left  associative  | r*  i*  s*  *..  /  div  mod
   Infix   right associative  | --..
   Infix   not   associative  | `..                             [*]
   Infix   right associative  | ==..
   Infix   right associative  | ||..
   Infix   right associative  | &&..
   Infix   left  associative  | #..
   Prefix  not   associative  | r~  i~  ~..
   Postfix not   associative  | ?..

(1) The left-hand side of ``==>`` and ``=!=>`` binds tighter than ``,``, so
``a, b ==> c, d`` reads ``a, (b ==> (c, d))``.

This is the table ``elpi -document-infix-syntax`` prints. To check how an
expression parses, run ``echo '…' | elpi -parse-term``.


Keywords
========

The following words are reserved and cannot be used as names: the declaration
and signature keywords ``kind``, ``type``, ``typeabbrev``, ``pred``, ``func``,
``external``, ``symbol``, ``macro``, ``namespace``, ``shorten``,
``accumulate``, ``constraint``, ``rule``, and the binders ``pi``, ``sigma`` and
``as``.

The words that follow a ``:`` to form an attribute are reserved too:
``:name``, ``:before``, ``:after``, ``:replace``, ``:remove`` and ``:if`` are
attributes of a rule; ``:index``, ``:functional``, ``:untyped`` and ``:nooc``
are attributes of a signature (see :doc:`declarations-and-attributes`).


The token grammar
=================

The character classes named above are, verbatim, the ones the ``ocamllex``
lexer uses:

.. literalinclude:: ../../../src/parser/lexer.mll.in
   :language: ocaml
   :start-at: let digit =
   :end-at: let symbcharplus

``num`` is an integer; ``num "." pnum`` or ``"." pnum`` is a float. A constant
name comes from exactly one of these productions (the keyword rules in between are elided):

.. code-block:: ocaml
   
   let constant =
      | "_" idchar+           
      | "_"                   
      | ucase idcharstar      
      | lcase idcharstarns    
      | "." idcharstarns      
      | '@' idcharstar        
      | '\'' symbcharstar '\''
      | '`'  symbcharstar '`' 

``idcharstarns`` is ``idcharstar`` extended with an embedded ``.`` before a
letter — that is what makes ``std.rev`` a single token. The last two are the
:ref:`quoted identifiers <quoted-identifiers>`. The bare ``_`` is the anonymous
variable; the other seven productions all yield one ``CONSTANT`` token, and the
compiler decides what it stands for from the first character: ``@`` a macro, an
upper-case letter a variable, otherwise a constant.


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
  … ; Elpi's operator set is fixed (`Operators`_).


Example
=======

.. elpi:: ../code/lexical.elpi
   :assert: items: 2 discount: -5
