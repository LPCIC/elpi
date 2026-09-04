############################
Embedding and extending Elpi
############################

Elpi is a library first: the ``elpi`` command-line tool
(:doc:`getting-started`) is itself a thin client of the ``elpi`` OCaml
package, and every host application — from a five-line script to coq-elpi,
the largest one — drives the same API.


Embedding
==========

Link with ``ocamlfind`` (``-package elpi``) or dune (``(libraries elpi)``).
Driving the interpreter is a handful of calls, in order: ``Setup.init``
builds an interpreter equipped with a set of builtins; ``Parse.program`` and
``Parse.goal`` read a program and a query from source text;
``Compile.program``, ``Compile.query`` and ``Compile.optimize`` produce a
runnable executable; ``Execute.once`` (or ``Execute.loop``, for a REPL) runs
it. ``elpi_REPL.ml``, the source of the ``elpi`` command itself, is the
canonical minimal client — every flag aside, it is exactly this sequence.


Extending: a builtin written in OCaml
========================================

The FFI shape of a builtin is ``MLCode (Pred (name, signature, function),
doc)``: ``signature`` describes each argument with ``In``/``Out``/``InOut``
(direction) and a *conversion* (how an Elpi term becomes an OCaml value and
back — ``string``, ``int``, ``list``, ``BuiltInData.any``, or one of your
own), and the OCaml function receives the ``In``/``InOut`` arguments already
converted and returns the ``Out``/``InOut`` ones. ``sys.file_exists``, one of
the simplest real builtins in Elpi's own standard library, needs only one
``In`` and no output at all — its two outcomes are: succeed (return ``()``),
or fail, by raising ``No_clause`` (an *output* argument that may or may not
be produced is wrapped with the ``!:`` / ``?:`` notation instead; see
``BuiltInPredicate.Notation`` in the API for the details):

.. literalinclude:: ../../src/builtin.ml
   :language: ocaml
   :lines: 497-507

A declaration list, built with ``BuiltIn.declare ~file_name``, bundles one or
more such predicates (and, optionally, plain doc strings or Elpi source via
``LPDoc``/``LPCode``) into a ``Setup.builtins`` value — the same kind of
value as ``Elpi.Builtin.std_builtins``, and passed to ``Setup.init`` the same
way, in a list alongside it:

.. literalinclude:: code/embedding-driver.ml
   :language: ocaml

Once ``my_builtins.elpi`` accumulates automatically wherever ``my_builtins``
is passed to ``Setup.init``, ``my_program.elpi`` can call ``sys.file_exists``
like any other predicate, with no further wiring on the Elpi side.


Also worth knowing
=====================

A **custom data type** — an OCaml value that should look like a plain Elpi
term rather than being converted through ``string``/``int``/``list`` — is
declared with ``MLData: 'a Conversion.t -> declaration``, giving Elpi a pair
of functions to read a term back into the OCaml value and to embed it as a
term. A **quotation** (:doc:`features/quotations`) is registered the same
way builtins are, through ``API.Quotation.set_default_quotation`` or
``register_named_quotation``, each given a parser from source text to a
term. **Extensible state** — data threaded through compilation and execution
that is not itself an Elpi term, such as a symbol table built while
compiling — is a ``State.component``, declared with
``API.State.declare_component`` and read and written through the ``state``
value every advanced FFI hook (``Full``, ``Read``, …) receives.

The odoc **API reference** (linked from this manual's sidebar) is the
complete signature of every module mentioned here; coq-elpi is the largest
real-world embedding, using custom data types, quotations and extensible
state alike to embed Rocq's own term syntax into Elpi.
