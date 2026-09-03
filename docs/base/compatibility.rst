##################################################
Compatibility with Teyjus, Prolog and legacy Elpi
##################################################

Elpi is a dialect of λProlog and runs most programs written for
`Teyjus <https://github.com/teyjus/teyjus>`_. Collected here are the
places where it deviates from Teyjus or from standard Prolog, and the older
Elpi syntax that newer spellings have superseded but that a program may
still be written in.


Lexical differences
===================

Elpi's tokens are close to those of `Teyjus
<https://github.com/teyjus/teyjus/wiki/TeyjusTokens>`_. Both share:

* the identifier character set: letters, digits and the sign characters
  ``+ - * / ^ < > = ` ' ? @ # $ & ! _ ~``;
* the rule for telling a variable from a constant: a leading ``_`` or
  upper-case letter marks a variable;
* the integer and real shapes: ``.5`` yes, ``3.`` no;
* the comments: ``%`` to end of line, nesting ``/* */``.

They differ in:

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

In Teyjus and standard λProlog, ``;`` is a special, built-in control
construct, not an ordinary predicate: the cut is *transparent* through it, so
a ``!`` written inside a disjunct is treated as if it were written in
the enclosing rule: it cuts that rule's own untried sibling rules too, not
just the other disjunct.

In Elpi, ``;`` genuinely *is* an ordinary (higher-order) predicate, actually
called as such through the two rules it is defined by, ``(A ; _) :- A.`` and
``(_ ; B) :- B.`` (:doc:`features/control-and-cut`), so it is a real call, one
more stack frame. A ``!`` written inside a disjunct only cuts back to *that*
call: it discards ``;``'s own untried alternative (the other disjunct) but,
unlike Teyjus, does not reach further out to cut the enclosing rule's own
sibling rules:

.. elpi:: code/cut-in-disjunct.elpi
   :assert: p's second rule fired\nafter p

``p``'s second rule still fires here: the ``!`` inside the first rule's
disjunct only prevented falling back to ``true``, not the whole first rule
from failing over to the second one.

Unification outside the pattern fragment (:doc:`features/unification-and-variables`)
aborts by default; Teyjus instead delays it as a constraint. Passing the
deprecated ``-delay-problems-outside-pattern-fragment`` flag restores that
behaviour.


Superseded Elpi keywords
=========================

Newer spellings have replaced several older Elpi keywords. The old ones still
parse and mean the same thing (:doc:`syntax/type-declarations`):

* ``kind name type -> … -> type`` is now ``data name A … Z``, one placeholder
  per parameter instead of one ``type ->``:

  .. code-block:: elpi

     data i32.        kind i32  type.
     data tree A.     kind tree type -> type.
     data map A B.    kind map  type -> type -> type.

  ``kind`` also takes a comma-separated list of names (``kind day, month type.``);
  ``data`` takes one name.
* ``type name <type>`` for a *data constructor* is now ``symb name <type>``;
  ``symbol`` is a slightly-less-old spelling of ``symb``. All three of

  .. code-block:: elpi

     symb  leaf tree A.
     symbol leaf tree A.       % or  symbol leaf : tree A.
     type  leaf tree A.

  declare the same constant, and all three take a comma-separated list of
  names (``type apple, pear item.``). ``symbol``, like ``symb``, also takes
  an optional ``:`` before the type; ``type`` does not.
* ``external`` before a declaration is now ``builtin``.
* A ``symb`` (or ``type``) whose type *ends in* ``prop`` is really a
  predicate: write it as a ``pred`` or ``func`` signature instead, so
  ``symb p int -> prop.`` becomes ``pred p int.`` (or ``func p int.`` when it
  is deterministic).
* The type ``prop``, and its λProlog spelling ``o``, is now ``(pred)``, with
  ``(func)`` for the deterministic case. ``fprop``, a former keyword for the
  latter, has been removed entirely: write ``(func)``.
* ``variadic T R`` in a type is the old spelling of a trailing ``..`` on the
  last argument (:doc:`syntax/type-declarations`): ``type f variadic int prop.``
  is now ``pred f int.. .`` (``func`` if deterministic).


Older signature forms
========================

``type name … -> prop`` gives a predicate a type with no mode information at
all: every argument is unified, none matched, since there is nothing marking
one as input. Older Elpi paired such a declaration with a separate
``mode (name i o).`` directive to add that information; this was never a
Teyjus or standard λProlog feature, only Elpi's own now-legacy syntax.
**Current Elpi does not parse ``mode`` as a directive at all.** It is not a
keyword, so ``mode (name i o).`` is read as an ordinary fact about a
predicate called ``mode``, and fails to type-check.

The ``i:`` / ``o:`` markers survive, but only *inline*, one before each
argument type, in place of the single ``->`` a modern signature uses
(:doc:`syntax/type-declarations`): ``pred name i:int, o:string.`` is the old
spelling of ``pred name int -> string.``. Unlike ``->`` they can also
*interleave* inputs and outputs (``:functional pred name o:A, i:A.``), the
one thing ``->`` cannot express, but that is discouraged: keep the outputs
last.

``:functional`` before a ``pred`` marks it deterministic, like the ``func``
keyword, which is preferred. It is still needed for a signature with
interleaved arguments as above, where ``func`` (which implies ``->``) cannot
be used.


The occur check
===============

Elpi performs the occur check by default: unifying a variable with a term
that already contains it fails, rather than building a cyclic term. SWI-Prolog
and ISO Prolog default the other way: ``occurs_check`` is ``false``, ordinary
``=/2`` builds the cyclic term, and a program that wants the check asks for it
per call with ``unify_with_occurs_check/2``. Elpi is the reverse: checked
everywhere, with the ``:nooc`` attribute opting one predicate out. The
attribute, the ``unsound_unif`` builtin and ``ground_term`` are described in
:doc:`features/unification-and-variables`.


Modules
========

A ``.sig`` file's *signature* (which names a module exports) is ignored; Elpi
has no separate notion of a module's public interface. ``import`` and
``accum_sig``/``use_sig`` are parsed, looking for a compiled ``.mod`` /
``.sig`` unit the way Teyjus would produce one, but Elpi has no such compiled
unit format to begin with, so in practice they never find anything to load;
``accumulate`` (:doc:`syntax/file-structure-and-attributes`) is the only way
to pull in another file's code. Elpi accumulates each file **once**, even if
several accumulated files each accumulate it too; Teyjus accumulates every
time, which duplicates rules and is rarely what one wants. Relative
``accumulate`` paths, and ``-I``, are
:doc:`syntax/file-structure-and-attributes`; the ``elpi`` command line tool
additionally reads the colon-separated
``TJPATH`` environment variable as a fallback search path, for compatibility
with Teyjus scripts that set it.
