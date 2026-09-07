#################
Type declarations
#################

Types play **no role at run time**: the type checker reads them, reports
mismatches, and they are then discarded. They still earn their keep — they let
the checker catch mistakes early, and some features such as spilling rely on
knowing a predicate's arity. A predicate with no signature draws a warning
(carrying a suggested one); an undeclared data constructor is an error. In
practice a program declares its vocabulary.

This chapter covers the declarations that introduce that vocabulary: ``data``
for type constructors, ``symb`` for data constructors, ``typeabbrev`` for
abbreviations, and ``pred`` / ``func`` for the **signature** of a predicate.
Older spellings of each are collected in :doc:`../compatibility`. The rules
written over the vocabulary are :doc:`inference-rules-and-queries`.


Data types
==========

``data`` introduces a new type or type constructor: a bare name for a type
with no parameters, or a name followed by one placeholder per parameter for a
type constructor. A placeholder's own spelling is irrelevant — only how many
there are matters — but this manual spells it like a type variable:

.. code-block:: elpi

   data i32.        % a type
   data tree A.     % a one-parameter type constructor
   data map A B.

One ``data`` takes a single name; the older spelling ``kind`` — which writes
the arity as one ``type ->`` per parameter, and does take a comma-separated
list of names — is in :doc:`../compatibility`.

A bare ``builtin`` may also prefix a ``data`` declaration; it is accepted for
symmetry with ``symb``/``pred``/``func`` but has no effect — ``data`` never
generates OCaml-side code, unlike those.

The types ``int``, ``string``, ``float`` and ``prop`` (the type of goals) are
built in, as are ``list``, ``pair`` and ``option``.


Data constructors
=================

``symb`` gives a constant a type. The arrow ``->`` is the function-space
constructor; an uppercase name in a type is a parameter, implicitly universally
quantified. The ``:`` between the name and the type is optional; this manual
usually omits it:

.. code-block:: elpi

   symb leaf tree A.
   symb node A -> tree A -> tree A -> tree A.

One ``symb`` can give the **same type to several constants** at once, their
names comma-separated. With more than one name the ``:`` earns its keep: it
says plainly where the names stop and the type starts, rather than leaving
that to whether a comma precedes the token —

.. code-block:: elpi

   symb alice, bob, carol : person.

means three constants of type ``person``. Without the ``:``,
``symb alice, bob, carol person.`` parses the same (``person``, with no comma
before it, is the type) but reads less clearly.

Two older spellings, ``symbol`` and ``type``, are still accepted; see
:doc:`../compatibility`.

A constant that the host application provides through the FFI is declared
``builtin symb name type`` (with a trailing ``= "variant"`` to pick one
overload) — see :doc:`../embedding`.

A predicate is always given a ``pred`` / ``func`` signature (next section),
never a plain ``symb`` whose type ends in ``prop`` — the λProlog way, kept
for compatibility (:doc:`../compatibility`).


Type abbreviations
==================

``typeabbrev`` names a type expression; the name is expanded at compile time.

.. code-block:: elpi

   typeabbrev int-tree (tree int).
   typeabbrev (assoc A) (list (pair string A)).

The parenthesised form ``(assoc A)`` is used when the abbreviation takes
parameters.


Predicate signatures
====================

A predicate is declared with ``pred`` or ``func``. The argument types are
listed comma-separated, and a single ``->`` splits the **input** arguments
(before it) from the **output** arguments (after it):

.. code-block:: elpi

   func append  list A, list A -> list A.  % two inputs, one output
   func size    tree A -> int.             % one input, one output

An input argument is *matched* against the pattern in each rule head; an output
argument is *unified*. What the distinction means operationally is
:doc:`../features/modes`. Exactly one ``->`` is allowed; the other two shapes
omit it:

.. code-block:: elpi

   func same-length  list A, list B.       % no arrow: every argument is an input
   pred ancestor  -> person, person.       % leading arrow: every argument is an output

A higher-order argument that is itself a signature must be parenthesised:

.. code-block:: elpi

   func map  list A, (func A -> B) -> list B.

``func`` differs from ``pred`` in one way: it also declares the predicate
**deterministic** — a call leaves no choice points — and this is checked.
Determinacy is described in :doc:`../features/determinacy-checking`.

``(pred)`` is the type of a predicate that takes no arguments — a goal. It is
also spelled ``prop``, or ``o`` in the λProlog tradition. ``(func)`` is the
same for a functional predicate. ``any`` matches any type.

A ``pred`` / ``func`` signature is a shorthand for a ``symb`` whose type is a
``(pred …)`` / ``(func …)``, so ``map`` above can equally be declared

.. code-block:: elpi

   symb map (func list A, (func A -> B) -> list B).

A predicate may be **overloaded** by repeating its signature with different
argument types. A defining rule then needs a type ascription (``(X : int)``)
only where its own arguments leave the overload ambiguous — a variable in a
position where the signatures differ; a literal there is enough on its own.
See :doc:`../features/types-and-type-checking`.


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

Variadic predicates are mostly an FFI concern. An older type-level spelling,
``variadic T R``, is in :doc:`../compatibility`.


Signature attributes
====================

Attributes written before a ``pred``, ``func`` or ``symb`` describe the
predicate itself:

* ``:index (…)`` chooses how the predicate is indexed for rule selection —
  :doc:`../features/argument-indexing`;
* ``:external``, or the bare keyword ``builtin`` before the declaration, says
  the predicate is implemented in OCaml through the FFI — :doc:`../embedding`;
* ``:nooc`` turns off the occur check for the predicate; it is described in
  :doc:`../compatibility`.

Attributes that graft or guard a *rule* (``:name``, ``:if``, ``:untyped``, …)
go on the rule, not the signature — :doc:`file-structure-and-attributes`.


Older spellings
---------------

Every construct above has an older, still-accepted spelling — ``kind`` for
``data``, ``symbol`` / ``type`` for ``symb``, ``external`` for ``builtin``,
``variadic T R`` for a trailing ``..``, the ``i:`` / ``o:`` mode markers and
``:functional`` for a ``pred`` / ``func`` signature, ``type name … -> prop``
for a predicate, and the standalone ``mode`` directive. They are collected,
with what maps to what, in :doc:`../compatibility`.


Example
=======

.. elpi:: ../code/type-declarations.elpi
   :assert: size 2 labels \[a, b\]
