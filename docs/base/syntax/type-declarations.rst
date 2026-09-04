#################
Type declarations
#################

Types play **no role at run time**: the type checker reads them, reports
mismatches, and they are then discarded. Every declaration in this chapter is
therefore optional — but a predicate you never declare draws a warning (with a
suggested signature), and a data constructor you never declare is an error, so
in practice a program declares its vocabulary.

This chapter covers the declarations that introduce that vocabulary: ``kind``
for type constructors, ``type`` for data constructors, ``typeabbrev`` for
abbreviations, and ``pred`` / ``func`` for the **signature** of a predicate.
The rules written over the vocabulary are :doc:`inference-rules-and-queries`.


Kinds
=====

``kind`` introduces a new type or type constructor. On the right, ``type`` is
the kind of a type that takes no parameters; each ``type ->`` in front adds a
parameter:

.. code-block:: elpi

   kind i32  type.                 % a type
   kind tree type -> type.         % a one-parameter type constructor
   kind map  type -> type -> type.

Several names may share a kind: ``kind day, month type.``. The types ``int``,
``string``, ``float`` and ``prop`` (the type of goals) are built in, as are
``list``, ``pair`` and ``option``.


Data constructors
=================

``type`` gives a constant its type. The arrow ``->`` is the function-space
constructor; an uppercase name in a type is a parameter, implicitly universally
quantified:

.. code-block:: elpi

   type leaf tree A.
   type node A -> tree A -> tree A -> tree A.

Several constants may share a type: ``type alice, bob, carol person.``.

``type`` is **not** used to declare a predicate. ``type p int -> prop.`` still
works — it is the λProlog spelling — but this manual always gives a predicate a
``pred`` / ``func`` signature instead; the older form is in
:doc:`../compatibility`.


Type abbreviations
==================

``typeabbrev`` names a type expression; the name is expanded at compile time.

.. code-block:: elpi

   typeabbrev int-tree (tree int).
   typeabbrev (assoc A) (list (pair string A)).

The parenthesised form ``(assoc A)`` introduces parameters.


Predicate signatures
====================

A predicate is declared with ``pred`` or ``func``. The argument types are
listed comma-separated, and a single ``->`` splits the **input** arguments
(before it) from the **output** arguments (after it):

.. code-block:: elpi

   pred append  list A, list A -> list A.  % two inputs, one output
   func size    tree A -> int.             % one input, one output

An input argument is *matched* against the pattern in each rule head; an output
argument is *unified*. What the distinction means operationally is
:doc:`../features/modes`. Exactly one ``->`` is allowed; the other two shapes
omit it:

.. code-block:: elpi

   pred same-length  list A, list B.       % no arrow: every argument is an input
   pred ancestor  -> person, person.       % leading arrow: every argument is an output

A higher-order argument that is itself a signature must be parenthesised:

.. code-block:: elpi

   func map  list A, (func A -> B) -> list B.

A trailing ``..`` makes the last output *variadic* — the predicate accepts that
argument any number of times: ``func f int, int -> int.. .`` is called with
three or four arguments. This is mostly used by FFI builtins.

``func`` differs from ``pred`` in one way: it also declares the predicate
**deterministic** — a call leaves no choice points — and this is checked.
``:functional`` on a ``pred`` says the same thing. A predicate with input and
output arguments *interleaved* cannot use the ``->`` form; it keeps the legacy
``i:`` / ``o:`` markers together with ``:functional``. Determinacy is
:doc:`../features/determinacy-checking`.

A predicate may be **overloaded** by repeating its signature with different
argument types; each defining rule then needs a type ascription to say which
one it belongs to. See :doc:`../features/types-and-type-checking`.

In a type, ``prop`` is the type of a goal (``o`` is accepted as an alias),
``any`` matches any type, and ``variadic T R`` is the type of a construct that
takes any number of ``T`` arguments to build an ``R`` (``,`` has that type).


Signature attributes
====================

Attributes written before a ``pred`` / ``func`` / ``type`` describe the
predicate itself:

* ``:index (…)`` chooses how the predicate is indexed for rule selection —
  :doc:`../features/argument-indexing`;
* ``:functional`` marks a ``pred`` deterministic, exactly like ``func``;
* ``:external``, or the bare keyword ``external`` before the declaration, says
  the predicate is implemented in OCaml through the FFI — :doc:`../embedding`.

``:nooc``, which turns off the occur check for one predicate, is in
:doc:`../compatibility`. Attributes that graft or guard a *rule* (``:name``,
``:if``, ``:untyped``, …) go on the rule, not the signature —
:doc:`file-structure-and-attributes`.

The ``symbol`` keyword is a variant of ``type`` that ascribes a type to an
operator symbol (``external symbol`` for an FFI one); it is used mostly in the
standard library.


Example
=======

.. elpi:: ../code/type-declarations.elpi
   :assert: size 2 labels \[a, b\]
