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
:doc:`terms-and-operators` and :doc:`inference-rules-and-queries`.

To see how a piece of source is tokenised and parsed, run
``echo '…' | elpi -parse-term``.


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

(a run made only of symbol characters is instead read as a mixfix operator — see
`Operators`_ below).

The **first character decides the role of the name**:

* a name starting with an **uppercase letter** is a **unification variable** —
  ``X``, ``Acc``, ``Result1`` (a name starting with ``_`` is also variable-like,
  but a *wildcard* — see below);
* every other name is a **constant** — a predicate or a term constructor:
  ``append``, ``red``, ``std.length``, ``make-palindrome``.

A name may not *start* with ``-`` or a digit, but it may *contain* them: a
lowercase-initial name like ``make-palindrome`` or ``v1`` is a single token.
Write ``X - Y`` (with spaces) for subtraction.

.. rubric:: Qualified names

A ``.`` immediately followed by a letter is part of the name: ``std.list.map``
is a single constant, not ``std`` applied to ``list.map``. A name written with
a **leading** ``.`` is looked up in the global scope, ignoring any enclosing
``namespace`` — inside ``namespace n`` the name ``.p`` is the top-level ``p``,
not ``n.p``. Namespaces and these qualified names are covered in
:doc:`../features/program-organization`. A ``.`` *not* followed by a letter is
the full stop that ends a rule or directive.

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

A run of *identifier* characters enclosed in back-quotes or single quotes, with **no spaces**
inside. It is not a string, and on its own it is not a constant: it is an
identifier that the host application can choose to *compile* in a special way.
It looks like a string but can be given, for instance, case-insensitive
comparison. Quoting is also the only way to write an identifier that contains
``:`` or that begins with a symbol character.

.. code-block:: elpi

   X = `a:b`,
   Y = 'CamelCase'.

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
character — that is what lets ```foo``` and ``'foo'`` be read as
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

This is the table ``elpi -document-infix-syntax`` prints.


Keywords
========

The following words are reserved and cannot be used as names: the declaration
and signature keywords ``data``, ``type``, ``typeabbrev``, ``pred``, ``func``,
``symb``, ``builtin``, ``macro``, ``namespace``, ``shorten``, ``accumulate``,
``constraint``, ``rule``, and the binders ``pi``, ``sigma`` and ``as``. The
superseded spellings ``kind``, ``symbol`` and ``external`` (:doc:`../compatibility`)
are reserved too.

The words that follow a ``:`` to form an attribute are reserved too:
``:name``, ``:before``, ``:after``, ``:replace``, ``:remove``, ``:if`` and
``:untyped`` are attributes of a rule; ``:index``, ``:functional`` and
``:nooc`` are attributes of a signature (see :doc:`type-declarations`).

Example
=======

.. elpi:: ../code/lexical.elpi
   :assert: items: 2 discount: -5

The reference tokenizer 
=======================

The character classes named above are, verbatim, the ones the ``ocamllex``
lexer uses:

.. literalinclude:: ../../../src/parser/lexer.mll.in
   :language: ocaml
   :start-at: let digit =
   :end-at: let symbcharplus

``num`` is an integer; ``num "." pnum`` or ``"." pnum`` is a float. An
identifier comes from exactly one of these productions (the keyword rules in
between are elided):

.. code-block:: ocaml

   let identifier =
      | "_" idchar+               (* wildcard (linear unification variable)  *)
      | "_"                       (* wildcard (linear unification variable)  *)
      | ucase idcharstar          (* unification variable                    *)
      | lcase idcharstarns        (* constant                                *)
      | "." idcharstarns          (* namespace escaping                      *)
      | '@' idcharstar            (* macro                                   *)
      | '\'' symbcharstar '\''    (* quoted identifier                       *)
      | '`'  symbcharstar '`'     (* quoted identifier                       *)

``idcharstarns`` is ``idcharstar`` extended with an embedded ``.`` before a
letter — that is what makes ``std.rev`` a single token. The last two are the
:ref:`quoted identifiers <quoted-identifiers>`. The bare ``_`` is the anonymous
variable; the other seven productions all yield one ``CONSTANT`` token, and the
compiler decides what it stands for from the first character: ``@`` a macro, an
upper-case letter a variable, otherwise a constant.

How these conventions differ from Teyjus and from standard Prolog is covered in
:doc:`../compatibility`.


