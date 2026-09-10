############################
Embedding and extending Elpi
############################

Elpi is a library first: the ``elpi`` command-line tool
(:doc:`getting-started`) is itself a thin client of the ``elpi`` OCaml
package, and every host application, from a five-line script to coq-elpi (the
largest one), drives the same API.


Embedding
==========

Link with ``ocamlfind`` (``-package elpi``) or dune (``(libraries elpi)``).
Driving the interpreter is a handful of calls, in order: ``Setup.init``
builds an interpreter equipped with a set of builtins; ``Parse.program`` and
``Parse.goal`` read a program and a query from source text;
``Compile.program``, ``Compile.query`` and ``Compile.optimize`` produce a
runnable executable; ``Execute.once`` (or ``Execute.loop``, for a REPL) runs
it. ``elpi_REPL.ml``, the source of the ``elpi`` command itself, is the
canonical minimal client: every flag aside, it is this sequence.


Extending: a builtin written in OCaml
========================================

The FFI shape of a builtin is ``MLCode (Pred (name, signature, function),
doc)``: ``signature`` describes each argument with ``In``/``Out``/``InOut``
(direction) and a *conversion* (how an Elpi term becomes an OCaml value and
back: ``string``, ``int``, ``list``, ``BuiltInData.any``, or one of your
own), and the OCaml function receives the ``In``/``InOut`` arguments already
converted and returns the ``Out``/``InOut`` ones. ``sys.file_exists``, one of
the simplest real builtins in Elpi's own standard library, needs only one
``In`` and no output at all: its two outcomes are to succeed (return ``()``)
or to fail by raising ``No_clause`` (an *output* argument that may or may not
be produced is wrapped with the ``!:`` / ``?:`` notation instead; see
``BuiltInPredicate.Notation`` in the API for the details):

.. literalinclude:: ../../src/builtin.ml
   :language: ocaml
   :lines: 497-507

A declaration list, built with ``BuiltIn.declare ~file_name``, bundles one or
more such predicates (and, optionally, plain doc strings or Elpi source via
``LPDoc``/``LPCode``) into a ``Setup.builtins`` value, the same kind of
value as ``Elpi.Builtin.std_builtins``, and passed to ``Setup.init`` the same
way, in a list alongside it:

.. literalinclude:: code/embedding-driver.ml
   :language: ocaml

Once ``my_builtins.elpi`` accumulates automatically wherever ``my_builtins``
is passed to ``Setup.init``, ``my_program.elpi`` can call ``sys.file_exists``
like any other predicate, with no further wiring on the Elpi side.


Extending: a quotation
========================

``{{ … }}`` (the *default* quotation) and ``{{:name … }}`` (a *named* one,
``name`` any run of non-space characters) let a term be written in a
different, custom syntax and turned into an Elpi term at compile time
(:doc:`syntax/terms`). A quotation is not built in: the host registers each
one through ``API.Quotation.set_default_quotation`` or
``register_named_quotation``, giving Elpi a parser from source text to a term.
With none registered, ``{{ … }}`` is the compile-time error "No default
quotation".

For its own testing the ``elpi`` command-line tool registers one named
quotation, also called ``elpi``, whose custom syntax is Elpi syntax itself: it
parses the quoted text as an ordinary term and hands it back unevaluated. That
is enough to show the mechanism, foreign-looking source turning into a term
the surrounding program can inspect and build on, even with Elpi standing in
for the foreign language:

.. elpi:: code/quotation.elpi
   :assert: 1 \+ 2

A quotation can also embed a piece of the surrounding Elpi program inside the
foreign syntax, an *antiquotation*. There is no fixed antiquotation syntax; it
is whatever the quotation's own parser recognises. coq-elpi quotes Rocq's term
syntax and antiquotes back to Elpi with an ``lp:`` prefix, so that in
``prod "x" t x\ {{ nat -> lp:x * bool }}`` the ``lp:x`` splices the
just-bound Elpi variable ``x`` into the quoted Rocq term.


Also worth knowing
=====================

A **custom data type**, an OCaml value that should look like a plain Elpi
term rather than being converted through ``string``/``int``/``list``, is
declared with ``MLData: 'a Conversion.t -> declaration``, giving Elpi a pair
of functions to read a term back into the OCaml value and to embed it as a
term. **Extensible state**, data threaded through compilation and execution
that is not itself an Elpi term, such as a symbol table built while
compiling, is a ``State.component``, declared with
``API.State.declare_component`` and read and written through the ``state``
value every advanced FFI hook (``Full``, ``Read``, …) receives.

The odoc **API reference** (linked from this manual's sidebar) is the
complete signature of every module mentioned here. Its landing page lists
several libraries; only ``elpi`` (the ``Elpi.API`` module used throughout
this chapter) is the public, supported one. The others,
``elpi.compiler``, ``elpi.parser``, ``elpi.runtime``, ``elpi.util``,
``elpi.lexer_config`` and ``elpi.trace.*``, are Elpi's own implementation,
split into separate libraries for internal build reasons and documented
there only incidentally; a host application should never depend on them
directly. coq-elpi is the largest real-world embedding, using custom data
types, quotations and extensible state alike to embed Rocq's own term
syntax into Elpi.
