###################
Lexical conventions
###################

An Elpi source file is read as a stream of bytes. At the top level it is a
sequence of *rules* and *directives*, each terminated by a full stop.
Whitespace (spaces, tabs, carriage returns and newlines) separates tokens and
is otherwise insignificant: indentation carries no meaning, and the
terminating ``.`` need not sit on a line of its own.

Outside string literals and comments only ASCII characters are used; a
non-ASCII byte there is a lexical error. Inside a string literal or a comment
any byte is accepted and passed through unchanged, so UTF-8 text can appear
there, but Elpi neither decodes nor validates it.

The rules for breaking source text into tokens follow. The grammar that
assembles those tokens into terms and rules is covered in :doc:`terms` and
:doc:`inference-rules-and-queries`. To see how a concrete piece of source is
tokenised and parsed, run it through ``echo '…' | elpi -parse-term``, which
prints the resulting term.


Comments
========

.. code-block:: elpi

   % a line comment runs to the end of the line

   /* a block comment,
      /* which may be nested */
      up to the matching close */

Block comments nest, so commenting out a region that already contains a
``/* … */`` pair works as expected: the inner close does not end the outer
comment.

A line comment whose text begins with ``elpi:`` is a directive to the lexer
rather than an ordinary comment. The three are ``% elpi:skip N`` (skip the
next ``N`` lines), ``% elpi:if version …`` and ``% elpi:endif``; they are
described in :doc:`rule-attributes`.


Identifiers
===========

An identifier starts with a letter or ``_`` and continues with any number of
letters, digits, ``_``, ``-``, ``$`` and the *symbol characters*

.. code-block:: text

   +  *  /  ^  <  >  `  '  ?  @  #  ~  =  &  !

The lexer is greedy: a maximal run of those characters is **one** identifier,
even when it contains something that reads like an operator. The characters
that are *not* identifier characters, namely whitespace and the punctuation
``, ; : | ( ) [ ] { } "``, are what ends one identifier and begins the next
token. A name is therefore glued together by ``+``, ``-``, ``>``, ``!``,
``@`` and the rest, but split apart by a comma or a colon:

.. code-block:: text

   a->b        one identifier   (write  a -> b  for the function space)
   n+1         one identifier   (write  n + 1   for the addition)
   foo!        one identifier
   foo@bar     one identifier   (@ is special only as the first character)
   foo.bar     one identifier   (a qualified name, see below)

   foo,bar     three tokens:   foo   ,   bar
   foo;bar     three tokens:   foo   ;   bar
   foo:bar     three tokens:   foo   :   bar

A run made *only* of symbol characters, with no leading letter, is not an
identifier at all: it is a mixfix operator, covered under `Operators`_ below.

An identifier may not *start* with ``-`` or a digit, although it may contain
them: ``make-palindrome`` and ``v1`` are each a single token. The everyday
consequence is that an infix operator written between two bare names needs
spaces around it: ``X - Y`` for subtraction, ``N = M`` for unification.
Without the spaces, ``X-Y`` and ``N=M`` are long names.

.. rubric:: Variables and constants

The **first character** of an identifier fixes its role, and no declaration
is needed to tell the two kinds apart:

* a name starting with an **uppercase letter** is a **unification variable**:
  ``X``, ``Acc``, ``Result1``. A name starting with ``_`` is variable-like
  too, but is a *wildcard* (see below);
* every other name is a **constant**, a predicate or a term constructor:
  ``append``, ``red``, ``std.length``, ``make-palindrome``.

.. rubric:: Qualified names

A ``.`` immediately followed by a letter is part of the name: ``std.list.map``
is a single constant, not ``std`` applied to ``list.map``. A name written with
a **leading** ``.`` is looked up in the global scope, ignoring any enclosing
``namespace``: inside ``namespace n`` the name ``.p`` is the top-level ``p``,
not ``n.p``. Namespaces and these qualified names are covered in
:doc:`file-structure-and-attributes`. A ``.`` that is *not* followed by a
letter is the full stop that ends a rule or directive.

.. rubric:: The wildcard

A bare ``_`` is a fresh anonymous variable. A name that *starts* with ``_``
(``_x``, ``_Acc``) is also a wildcard: a fresh variable each time it is
written, never one that can be referred to again. See
:doc:`../features/unification-and-variables`.

.. rubric:: Macro names

The character ``@`` starts a macro name. A name that *begins* with ``@``
always refers to a macro, which must have been defined with
``macro @name … :- ….``; it can appear nowhere else. (Anywhere other than the
first position, ``@`` is an ordinary identifier character, as the ``foo@bar``
example above shows.) See :doc:`file-structure-and-attributes`.


Literals
========

.. rubric:: Integers

A run of digits, optionally with a leading ``-`` and no space before the
first digit: ``0``, ``42``, ``-2``. Subtraction is the infix operator ``-``
and takes an operand on each side, as in ``5 - 2``.

.. rubric:: Floating point

A digit sequence, a ``.``, and another digit sequence: ``3.0``, ``-1.5``. The
leading digit sequence may be empty, so ``.5`` is a float; the trailing one
may not, so ``3.`` is the integer ``3`` followed by the full stop that ends
the rule. There is no exponent notation.

.. rubric:: Strings

Delimited by ``"``. A string literal may span several lines, the newline
being part of the string. The escapes ``\n``, ``\t``, ``\b``, ``\r``, ``\\``
and ``\"`` are recognised, and a doubled ``""`` stands for one ``"``. There
are no octal or hexadecimal escapes.

.. code-block:: elpi

   Msg = "he said ""hi"" and\nleft"

.. raw:: html

   <details class="elpi-fold" id="quoted-identifiers"><summary>Quoted identifiers</summary>

A run of *identifier* characters, ``:`` included, enclosed in back-quotes
or single quotes, with **no spaces** inside. A quoted identifier is not a
string, and on its own it is not an ordinary constant either: it is an
identifier that the host application may choose to *compile* in a special
way, for instance giving it case-insensitive comparison. It looks like a
string but behaves like a name. Quoting is also the only way to write an
identifier that contains a ``:``, or one that begins with a symbol character.

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

.. raw:: html

   </details>


Operators
=========

Operators are built in: there is no ``infix`` / ``prefix`` directive to
declare your own, as there is in Teyjus. An operator is written either as a
run of symbol characters (``=>``, ``::``, ``+``, …) or as one of the reserved
words ``is``, ``div`` and ``mod``; the comma ``,`` is an infix operator too
(conjunction), even though it is punctuation, not a symbol-character run.

.. rubric:: Token families

Precedence and associativity belong not to individual operators but to
**families**. A family is identified by its leading character(s): ``+-->``
belongs to the ``+`` family, ``*-->`` to the ``*`` family. Every token of a
family parses with the same precedence and associativity, and no declaration
is needed: ``x +--> y *--> z`` reads ``x +--> (y *--> z)`` because the ``*``
family binds tighter than the ``+`` family.

In the table below a family is written with a trailing ``..`` (``+..`` is "any
token starting with ``+``"); a bare entry is a *fixed* token, the sole member
of its family. A family marked ``[*]`` may not *end* with its starting
character, which is what lets ```foo``` and ``'foo'`` be read as
`quoted identifiers <#quoted-identifiers>`__ rather than operators.

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
   Infix   right associative  | =>                               (2)
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

(2) ``=>`` is the traditional λProlog spelling of implication, the same
connective as ``==>`` but binding *tighter* than ``,``. This manual uses
``==>`` throughout; see :doc:`inference-rules-and-queries`.

This is the table ``elpi -document-infix-syntax`` prints.


Keywords
========

The following words are reserved and cannot be used as names. The declaration
and signature keywords are ``data``, ``typeabbrev``, ``pred``, ``func``,
``symb``, ``builtin``, ``macro``, ``namespace``, ``shorten``, ``accumulate``,
``constraint`` and ``rule``; the binders are ``pi``, ``sigma`` and ``as``.
The legacy spellings ``kind``, ``type``, ``symbol`` and ``external`` are
reserved as well, and remain available (see :doc:`../compatibility`).

The words that follow a ``:`` to form an attribute are reserved in that
position too: ``:name``, ``:before``, ``:after``, ``:replace``, ``:remove``,
``:if`` and ``:untyped`` on a rule; ``:index``, ``:functional`` and ``:nooc``
on a signature (see :doc:`type-declarations`). Outside an attribute the same
words (``name``, ``if``, ``index`` and so on) are ordinary constants; the
builtin ``name``, for one, relies on that.

The reference tokenizer
=======================

The character classes named above are, verbatim, the ones the ``ocamllex``
lexer uses:

.. literalinclude:: ../../../src/parser/lexer.mll.in
   :language: ocaml
   :start-at: let digit =
   :end-at: let symbcharplus

``num`` is an integer; ``num "." pnum`` or ``"." pnum`` is a float. An
identifier comes from one of these productions (the keyword rules in
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
letter, which is what makes ``std.rev`` a single token. The last two
productions are the `quoted identifiers <#quoted-identifiers>`__. The bare
``_`` is the anonymous variable; the other seven productions all yield one
``CONSTANT`` token, and the compiler decides what it stands for from the
first character: ``@`` a macro, an upper-case letter a variable, otherwise a
constant.

How these conventions differ from Teyjus and from standard Prolog is covered
in :doc:`../compatibility`.

Nested block comments, the wildcard, a qualified name, a negative integer
literal and a two-line string, in one small program:

.. elpi:: ../code/lexical.elpi
   :assert: items: 2 discount: -5
