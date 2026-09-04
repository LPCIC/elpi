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


.. note::

   **Stub — still to write:**

   * The semantic and module incompatibilities from ``INCOMPATIBILITIES.md``.
   * The older signature forms kept for compatibility: ``type name … -> prop``,
     the ``mode (name i o)`` directive and the ``i:`` / ``o:`` argument markers
     — how they map onto the modern ``pred`` / ``func`` ``In.. -> Out..``
     signatures, and the one case still needed today
     (``:functional pred name o:.., i:..`` for a signature whose input and
     output arguments are interleaved).
   * The ``:nooc`` attribute: unification does an occur check by default (Prolog
     does not); ``:nooc`` turns it off for one predicate. Example from the
     standard library, ``std.unsound_unif``:

     .. code-block:: elpi

        % Unification without occur check. It can create infinite terms.
        :nooc
        func unsound_unif -> A, A.
        unsound_unif X X.

     Guard code that disables the occur check against building cyclic terms
     with ``ground_term``. See also *Unification and variables*.

   Source material: ``INCOMPATIBILITIES.md``; ``src/builtin_stdlib.elpi``;
   ELPI.md “Mode and type declaration” / “Occur check”.
