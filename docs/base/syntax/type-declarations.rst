#################
Type declarations
#################

Types play **no role at run time**: the type checker reads them, reports
mismatches, and they are then discarded. They still earn their keep — they let
the checker catch mistakes early, and some features such as spilling rely on
knowing a predicate's arity. A predicate with no signature draws a warning
(carrying a suggested one); an undeclared data constructor is an error. In
practice a program declares its vocabulary.

This chapter covers the declarations that introduce that vocabulary: ``kind``
for type constructors, ``symbol`` (or ``type``) for data constructors,
``typeabbrev`` for abbreviations, and ``pred`` / ``func`` for the **signature**
of a predicate. The rules written over the vocabulary are
:doc:`inference-rules-and-queries`.


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

``symbol`` gives a constant a type. The arrow ``->`` is the function-space
constructor; an uppercase name in a type is a parameter, implicitly universally
quantified:

.. code-block:: elpi

   symbol leaf : tree A.
   symbol node : A -> tree A -> tree A -> tree A.

Several constants may share a type: ``symbol alice, bob, carol : person.``.

The older spelling ``type name <type>`` — no colon — is inherited from λProlog
and means exactly the same; it is still common and is not going away:

.. code-block:: elpi

   type leaf tree A.
   type node A -> tree A -> tree A -> tree A.

A constant that the host application provides through the FFI is declared
``external symbol name : type`` (with a trailing ``= "variant"`` to pick one
overload); see :doc:`../embedding`.

``type p int -> prop.`` also declares a *predicate*, the λProlog way, but this
manual always uses a ``pred`` / ``func`` signature instead (next section); the
older form is in :doc:`../compatibility`.


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

A ``pred`` / ``func`` signature is a shorthand for a ``symbol`` whose type is a
``(pred …)`` / ``(func …)``, so ``map`` above can equally be declared

.. code-block:: elpi

   symbol map : (func list A, (func A -> B) -> list B).

A predicate may be **overloaded** by repeating its signature with different
argument types; each defining rule then needs a type ascription to say which
one it belongs to. See :doc:`../features/types-and-type-checking`.


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

``variadic T R`` is the legacy type-level spelling for the same thing, still
used by builtins such as ``print`` and ``halt``. Variadic predicates are
otherwise mostly an FFI concern.


Signature attributes
====================

Attributes written before a ``pred``, ``func``, ``symbol`` or ``type`` describe
the predicate itself:

* ``:index (…)`` chooses how the predicate is indexed for rule selection —
  :doc:`../features/argument-indexing`;
* ``:external``, or the bare keyword ``external`` before the declaration, says
  the predicate is implemented in OCaml through the FFI — :doc:`../embedding`;
* ``:nooc`` turns off the occur check for the predicate; it is described in
  :doc:`../compatibility`.

Attributes that graft or guard a *rule* (``:name``, ``:if``, ``:untyped``, …)
go on the rule, not the signature — :doc:`file-structure-and-attributes`.


Legacy forms
------------

Two older ways of writing a signature are still accepted:

* ``:functional`` before a ``pred`` marks it deterministic, exactly like
  writing ``func`` — which is preferred.
* ``i:`` / ``o:`` markers, one per argument, in place of the single ``->``:
  ``pred append i:list A, i:list A, o:list A.``. Unlike ``->`` they let input
  and output arguments be *interleaved* (``:functional pred p o:A, i:A.``), but
  that is discouraged — keep the outputs last and use ``->``.

The ``type name … -> prop`` predicate form, and how it relates to the
standalone ``mode`` directive of standard λProlog (which current Elpi does
not actually parse as a directive at all — :doc:`../compatibility`), are in
:doc:`../compatibility`.


Example
=======

.. elpi:: ../code/type-declarations.elpi
   :assert: size 2 labels \[a, b\]
