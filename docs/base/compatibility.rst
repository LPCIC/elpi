####################################
Compatibility with Teyjus and Prolog
####################################

Elpi is a dialect of λProlog and runs most programs written for
`Teyjus <https://github.com/teyjus/teyjus>`_. This chapter collects the
places where it deviates from Teyjus or from standard Prolog.


Lexical differences
===================

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
* **Operators.** Teyjus programs declare operators with ``infix`` / ``prefix`` /
  … ; Elpi's operator set is fixed (see :doc:`syntax/lexical-conventions`).

See :doc:`syntax/lexical-conventions` for the full lexical rules.


Semantic differences
======================

``;`` is not an ordinary predicate, despite being *defined* by two rules,
``(A ; _) :- A.`` and ``(_ ; B) :- B.`` — the parser and the cut treat it as
part of the enclosing rule, which is why ``!`` reaches through it
(:doc:`features/control-and-cut`) instead of stopping at what looks like a
call boundary.

Unification outside the pattern fragment (:doc:`features/unification-and-variables`)
aborts by default; Teyjus instead delays it as a constraint. Passing the
deprecated ``-delay-problems-outside-pattern-fragment`` flag restores that
behaviour.


Older signature forms
========================

``type name … -> prop`` gives a predicate a type with no mode information at
all — every argument is unified, none matched, since there is nothing marking
one as input. Standard λProlog and Teyjus pair such a declaration with a
separate ``mode (name i o).`` directive to add that information; **current
Elpi does not parse ``mode`` as a directive at all** — it is not a keyword,
so ``mode (name i o).`` is read as an ordinary fact about a predicate called
``mode``, and fails to type-check. The ``i:`` / ``o:`` markers survive, but
only *inline*, inside the signature itself
(:doc:`syntax/type-declarations`'s legacy forms): ``pred name i:int, o:string.``
is the modern equivalent of the pair above, and remains the only way to
write a signature whose input and output arguments are interleaved
(``:functional pred name o:A, i:A.``).


The ``:nooc`` attribute
==========================

Unification performs the occur check by default, unlike Prolog: assigning a
variable to a term containing itself fails rather than building a cyclic
term. ``:nooc`` turns this off for one predicate — the builtin
``unsound_unif`` is defined exactly that way:

.. code-block:: elpi

   % Unification without occur check. It can create infinite terms.
   :nooc
   func unsound_unif -> A, A.
   unsound_unif X X.

.. elpi:: code/nooc.elpi
   :assert: = rejects X = f X \(occur check\)\nunsound_unif Y \(f Y\) succeeds

Code that relies on ``:nooc`` should guard against actually building a cyclic
term — ``ground_term`` (:doc:`features/unification-and-variables`), and most
other traversals, will not terminate on one.


Modules
========

A ``.sig`` file's *signature* (which names a module exports) is ignored — Elpi
has no separate notion of a module's public interface. ``import`` and
``accum_sig``/``use_sig`` are parsed, looking for a compiled ``.mod`` /
``.sig`` unit the way Teyjus would produce one, but Elpi has no such compiled
unit format to begin with, so in practice they never find anything to load;
``accumulate`` (:doc:`syntax/file-structure-and-attributes`) is the only way
to pull in another file's code. Elpi accumulates each file **once**, even if
several accumulated files each accumulate it too — Teyjus accumulates every
time, which duplicates rules and is rarely what one wants. Relative
``accumulate`` paths, and ``-I``, are :doc:`features/program-organization`;
the ``elpi`` command line tool additionally reads the colon-separated
``TJPATH`` environment variable as a fallback search path, for compatibility
with Teyjus scripts that set it.
