.. Elpi documentation master file.
   The full table of contents is built from the toctree directives below.

Elpi — Embeddable λProlog Interpreter
=====================================

Elpi is an embeddable implementation of `λProlog
<http://www.lix.polytechnique.fr/~dale/lProlog/>`_ extended with Constraint
Handling Rules (CHR). It is a logic programming language well suited to
manipulate abstract syntax trees with binders and unification variables, the
kind of data the *elaborator* of an interactive theorem prover works with. Elpi
is designed to be embedded into larger applications written in OCaml as an
extension language, and it comes with an API to drive the interpreter and a
foreign function interface (FFI) to add built-in predicates and data types.

This manual describes Elpi's syntax, its execution model (including CHR), every
language feature, the standard library and built-in predicates, the debugging
and tracing tools, and the OCaml API used to embed and extend the interpreter.
It assumes familiarity with λProlog; the reference for standard λProlog is
:ref:`Programming with Higher-Order Logic, by Miller and Nadathur <bib-miller-nadathur>`.

.. toctree::
   :maxdepth: 2
   :caption: Overview

   introduction
   getting-started

.. toctree::
   :maxdepth: 2
   :caption: Syntax

   syntax/lexical-conventions
   syntax/terms
   syntax/type-declarations
   syntax/inference-rules-and-queries
   syntax/constraint-handling-rules
   syntax/file-structure-and-attributes
   syntax/rule-attributes

.. toctree::
   :maxdepth: 2
   :caption: Semantics

   semantics/overview
   semantics/logic-programming-model
   semantics/constraints
   semantics/chr
   semantics/formal-semantics

.. toctree::
   :maxdepth: 2
   :caption: Language features

   features/unification-and-variables
   features/binders-and-hoas
   features/control-and-cut
   features/spilling
   features/types-and-type-checking
   features/determinacy-checking
   features/argument-indexing
   features/pitfalls

.. toctree::
   :maxdepth: 2
   :caption: Examples

   examples/stlc
   examples/hindley-milner

.. toctree::
   :maxdepth: 2
   :caption: Libraries

   builtins
   standard-library

.. toctree::
   :maxdepth: 2
   :caption: Debugging & tooling

   debugging-and-tracing

.. toctree::
   :maxdepth: 2
   :caption: Embedding and extending

   embedding

.. toctree::
   :maxdepth: 2
   :caption: Reference

   compatibility
   bibliography

.. toctree::
   :maxdepth: 1
   :caption: API

   elpi <elpi/index.html#http://>
