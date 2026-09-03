#################
Type declarations
#################

Types play no role at run time: the type checker reads them, reports
mismatches, and they are then discarded. They still earn their keep three
ways. They let the checker catch mistakes early. They resolve an overloaded
name, whose meaning depends on the types of the arguments it is applied to
(:doc:`../features/types-and-type-checking`). And some features, spilling
among them, rely on knowing a predicate's arity, which only a signature
records. A predicate with no signature draws a warning (carrying a suggested
one); an undeclared data constructor is an error. In practice a program
declares its vocabulary.

The declarations that introduce that vocabulary are ``data`` for type
constructors, ``symb`` for data constructors, ``typeabbrev`` for
abbreviations, and ``pred`` / ``func`` for the signature of a predicate.
Older spellings of each are collected in :doc:`../compatibility`. The rules
written over the vocabulary are covered in :doc:`inference-rules-and-queries`.


Data types
==========

``data`` introduces a new type or type constructor: a bare name for a type
with no parameters, or a name followed by one placeholder per parameter for a
type constructor. A placeholder's own spelling is irrelevant, only how many
there are, but this manual writes each as a type variable:

.. code-block:: elpi

   data i32.        % a type
   data tree A.     % a one-parameter type constructor
   data dict K V.   % a two-parameter type constructor

Each ``data`` declaration introduces exactly one name; ``data a, b.`` is a
syntax error. A ``data`` declaration may be prefixed with a bare ``builtin``,
for uniformity with ``symb`` / ``pred`` / ``func``, but on ``data`` the
parser accepts the keyword and then ignores it.

Three built-in types are *opaque*: ``int``, ``string`` and ``float`` are
backed directly by OCaml values. They have literal syntax (``42``, ``"hi"``,
``3.14``) but no constructors to take apart and no structure to match on; a
string, in particular, is not a list of characters. There is no character
type at all; a one-character string stands in for one. Everything done with
an opaque value goes through a builtin (:doc:`../builtins`). The container
types ``list`` (with its ``[…]`` syntax), ``option`` and ``pair`` come from
the standard prelude, and are documented in :doc:`../builtins`.


Data constructors
=================

``symb`` gives a constant a type. The arrow ``->`` is the function-space
constructor; an uppercase name in a type is a parameter, implicitly universally
quantified. The ``:`` between the name and the type is optional; this manual
usually omits it:

.. code-block:: elpi

   symb leaf tree A.
   symb node A -> tree A -> tree A -> tree A.

One ``symb`` can give the same type to several constants at once, their names
comma-separated. With more than one name the ``:`` earns its keep: it says
plainly where the names stop and the type starts, rather than leaving that to
whether a comma precedes the token:

.. code-block:: elpi

   symb alice, bob, carol : person.

means three constants of type ``person``. Without the ``:``,
``symb alice, bob, carol person.`` parses the same way (``person``, the token
with no comma before it, is the type) but reads less clearly.

Two older spellings, ``symbol`` and ``type``, are still accepted; see
:doc:`../compatibility`.

A constant that the host application provides through the FFI is declared
``builtin symb name type``, optionally with a trailing ``= "variant"`` that
selects one OCaml implementation among several (:doc:`../embedding`).

``symb`` is for data constructors only. A predicate is declared with a
``pred`` or ``func`` signature, the subject of the next section.


Type abbreviations
==================

``typeabbrev`` names a type expression; the name is expanded at compile time,
so it is a shorthand, not a new type: a value of type ``int-tree`` and one of
type ``(tree int)`` are interchangeable.

.. code-block:: elpi

   typeabbrev int-tree (tree int).
   typeabbrev (assoc A) (list (pair string A)).

The parenthesised form ``(assoc A)`` is used when the abbreviation itself
takes parameters.


Predicate signatures
====================

A predicate is declared with ``pred`` or ``func``. The argument types are
listed comma-separated, and a single ``->`` splits the *input* arguments
(before it) from the *output* arguments (after it):

.. code-block:: elpi

   func append  list A, list A -> list A.  % two inputs, one output
   func size    tree A -> int.             % one input, one output

An input argument is *matched* against the pattern in each rule head; an output
argument is *unified*. What the distinction means operationally is covered in
:doc:`../semantics/constraints`. Exactly one ``->`` is allowed; the other two
shapes omit it:

.. code-block:: elpi

   func same-length  list A, list B.       % no arrow: every argument is an input
   pred ancestor  -> person, person.       % leading arrow: every argument is an output

A higher-order argument, one that is itself a predicate or a function, must
be parenthesised, whether it is written as a bare arrow type or as a nested
signature:

.. code-block:: elpi

   func map  list A, (func A -> B) -> list B.

``func`` differs from ``pred`` in one way: it also declares the predicate
*deterministic*, meaning a call leaves no choice points, and this is checked.
Determinacy is described in :doc:`../features/determinacy-checking`.

``(pred)`` is the type of a goal: a predicate applied to all its arguments,
or one that takes none. ``(func)`` is the same for a functional predicate. A
signature with arguments builds on these: ``(pred A -> B)`` is the type
``A -> B -> (pred)`` of a two-argument predicate, and additionally records
that the first argument is an input and the second an output.

``any`` is a type that unifies with every other type. It switches type
checking off for the argument it covers, so it is used sparingly, chiefly in
the signatures of builtins that are polymorphic in a way the checker cannot
otherwise express.

A ``pred`` / ``func`` signature is a shorthand for a ``symb`` whose type is a
``(pred …)`` / ``(func …)``, so ``map`` above can equally be declared

.. code-block:: elpi

   symb map (func list A, (func A -> B) -> list B).

The two elaborate to the same signature and are checked the same way; the
``pred`` / ``func`` form is the idiomatic one and the only one this manual
uses.

A predicate may be *overloaded* by repeating its signature with different
argument types. A defining rule then needs a type ascription (``(X : int)``)
only where its own arguments leave the overload ambiguous, that is, a variable
in a position where the signatures differ. A literal in that position may pin
the type down by itself. See :doc:`../features/types-and-type-checking`.


Variadic predicates
-------------------

A trailing ``..`` after the last argument makes it *variadic*: the predicate
accepts that argument any number of times.

.. code-block:: elpi

   func divmod int, int -> int.. .         % here, called with three or four arguments

The defining rules then have heads of different arities, one per accepted
length:

.. code-block:: elpi

   divmod N D R    :- R is N div D.                  % three arguments
   divmod N D R M  :- divmod N D R, M is N mod D.    % four arguments

Variadic predicates are mostly an FFI concern; ``print``, for one, accepts
however many arguments it is passed.


Signature attributes
====================

An attribute written before a ``pred`` or ``func`` describes the predicate
itself:

* ``:index (…)`` chooses how the predicate is indexed for rule selection
  (:doc:`../features/argument-indexing`);
* ``:external``, or the bare keyword ``builtin``, says the predicate is
  implemented in OCaml through the FFI (:doc:`../embedding`). The same keyword
  may precede a ``symb`` that names an FFI constructor;
* ``:nooc`` turns off the occur check for the predicate; it is described in
  :doc:`../features/unification-and-variables`.

Attributes that graft or guard a *rule* (``:name``, ``:if``, ``:untyped``, …)
go on the rule, not the signature (:doc:`file-structure-and-attributes`).


Older spellings
---------------

Every construct above has an older, still-accepted spelling: ``kind`` for
``data``, ``symbol`` / ``type`` for ``symb``, ``external`` for ``builtin``,
``variadic T R`` for a trailing ``..``, the ``i:`` / ``o:`` mode markers and
``:functional`` for a ``pred`` / ``func`` signature, ``type name … -> prop``
for a predicate, and the standalone ``mode`` directive. They are collected,
with what maps to what, in :doc:`../compatibility`.


A worked set of declarations
============================

The program below declares a parametric ``data`` type, its constructors, a
``typeabbrev``, and two predicates over trees. ``size`` is a ``func``: every
call has one answer. ``has-label`` is only a ``pred``: its ``node`` case is
covered by three overlapping rules (the label may be at the node itself, in
the left subtree, or in the right), so the search for a label can succeed by
more than one path and a call may leave a choice point behind. It could not be
declared ``func``, even though ``main`` here calls it only once.

.. elpi:: ../code/type-declarations.elpi
   :assert: size is 3 and a is a label
