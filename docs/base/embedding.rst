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
   :start-at: MLCode (Pred ("sys.file_exists",
   :end-at: DocAbove);

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


Deriving conversions: ppx_elpi
================================

Writing by hand the conversion of an OCaml data type, and the matching
declaration on the Elpi side, is repetitive. Attaching the deriver
``[@@deriving elpi]`` of the ``ppx_elpi`` package to a type declaration
synthesizes the conversion of the type, of type
``Elpi.API.ContextualConversion.t`` and with all the glue needed to handle
data types with binders, the matching Elpi declaration and a deep copy
function for the type; it is enabled by preprocessing a module with the ppx in
the ``dune`` file, as in the following one, where the ppx is enabled on the
module ``my_code.ml`` only:

.. literalinclude:: code/ppx-example.dune
   :language: scheme

Three kinds of OCaml types are supported:

- **opaque** types, such as ``type t``, or a type with a definition that is
  not meant to be exposed to Elpi (see ``[@@elpi.opaque e]`` below); phantom
  parameters are not supported;
- **aliases**, such as ``type 'a t = ('a * int) list``;
- **algebraic** types, such as ``type t = K | S``. An algebraic type has one
  of two roles: a *datum*, that is a syntax tree, possibly with binders, or the
  *context* of a datum. A datum with binders needs one or more context types
  describing the information attached to its bound variables.

The type must come with a pretty printer named after the usual convention
(``pp`` if the type is called ``t``, ``pp_ty`` for a type called ``ty``).
Deriving both ``show`` (from ``ppx_deriving``, hence the ``ppx_deriving.show``
above) and ``elpi``, as in ``[@@deriving show, elpi]``, is the simplest way to
get one; see also ``[@@elpi.pp]``.


A first example: a parametric type
------------------------------------

The derived value has the name of the type. For a type with parameters it is
a function from the conversions of the parameters. With
``[@@deriving elpi { declaration = l }]`` the declarations of the derived
types are added to ``l``, created by ``Elpi.API.PPX.empty_declaration ()``.
``Elpi.API.PPX.to_list l`` gives the declarations, in the order they were
added, ready to be passed to ``BuiltIn.declare``:

.. literalinclude:: ../../ppx_elpi/tests/test_poly_adt.ml
   :language: ocaml
   :start-after: let file_name = Sys.argv.(1)
   :end-before: let () = Ppx_tests_lib

The Elpi declarations generated for it are the ones of the type and, since
``declaration`` also receives the ``LPCode`` of the string
``elpi__simple__deep_copy`` generated by the ppx, a *deep copy* function of the
type:
``func simple.copy (func X0 -> Y0), simple X0 -> simple Y0`` relates a value
to a copy of it, given a copy function for the parameter. The copy is the
identity: the generated rules just rebuild each constructor, calling the copy
function of the type (``name.copy``) on the fields of the same type and of the
parameters (``F0``), on the elements of lists through ``list.copy`` (an alias
of ``std.map``) and of the other standard containers through ``option.copy``,
``pair.copy``, ``triple.copy`` and ``quadruple.copy``, and through ``ty.copy`` on the
fields of any other type, which is assumed to exist. It does for the atomic
types of the standard library (``int.copy``, ``float.copy``, ``string.copy``,
``bool.copy``, ``loc.copy``, ``cmp.copy``, ``diagnostic.copy``,
``in_stream.copy`` and ``out_stream.copy`` are defined) and for the types
derived by the ppx: a type abbreviation is copied as its definition is, and an
opaque type by the identity. The name ``ty`` is the default Elpi name of the
type, so a type renamed with ``[@@elpi.type_code]`` is found only if it is
derived in the same block. The user is expected to place his own rules
*before* the generated ones, to override the cases he cares about and obtain a
non trivial copy, such as a substitution. No copy function is generated for
context types.

.. literalinclude:: ../../ppx_elpi/tests/test_poly_adt.expected.elpi
   :language: elpi


Data with binders and its context
-----------------------------------

A datum with binders is converted in a *context*: when a term is read back,
each bound variable is looked up in it, and when going under a binder a new
entry is added to it. A context type is an algebraic type whose constructors
each have exactly one field marked ``[@elpi.key "ty"]``: the key under which
the entry is stored, in a map built from the module given with
``[@@elpi.index (module M)]``. A context type is not a data type for Elpi:
each of its constructors is a function from a bound variable to the fields of
the entry, ``builtin func name ty -> field1, ..., fieldN``, where ``ty`` is the
Elpi type of the variables that the context describes (in the example,
``term``) and the fields are all the fields of the constructor, in order. The
key field can be anywhere among them. The entry of a variable is a rule of that
function, added to the program under the binder, for example
``entry x "x" tt ==> ...``.

In the example ``tctx`` is the context and ``term`` is the datum. A
``Var`` constructor is a bound variable of ``tctx`` (``[@elpi.var tctx]``),
and the ``Lam`` constructor binds a variable, adding an entry to ``tctx``
(``[@elpi.binder "term" tctx (fun b s -> Entry(s,b))]``). A builtin using
``term`` has to declare a context rich enough for it. It is declared with
``ContextualPred (name, in_ctx, ffi, f)`` instead of ``Pred``, where ``in_ctx`` is the
``in_ctx_for_term`` value generated for the type and ``ffi`` is a
``BuiltInPredicate.PPX.ffi``. It has the same constructors as the ``ffi`` of
``Pred`` (``In``, ``Out``, ``InOut``, ``Easy``, ``Read``, ``Full``, ``FullHO``
and the variadic ones), but its arguments are contextual conversions, and the
OCaml function ``f`` also receives the context and the constraints. The
context is an object whose methods, one per context type, give access to the
entries:

.. literalinclude:: ../../ppx_elpi/tests/test_simple_contextual.ml
   :language: ocaml
   :start-after: let file_name = Sys.argv.(1)
   :end-before: let () = Ppx_tests_lib

The Elpi declarations generated for it, followed by the signature of the
builtin, are:

.. literalinclude:: ../../ppx_elpi/tests/test_simple_contextual.expected.elpi
   :language: elpi

The deep copy of a datum with binders goes under the binders. A field below a
binder is copied under the binder, in the context extended with the entry of
the bound variable, which is copied to itself, as in
``pi x\ entry x B1 B0 ==> term.copy x x ==> term.copy (A2 x) (B2 x)`` (see the
``term.copy`` rules of the example above). Here ``entry`` is the constructor
built by the function of the binder, ``B1`` and ``B0`` are the copies of the
fields that the function receives, and ``term`` is the type of the bound
variable, the first argument of ``[@elpi.binder]``, which must come with its
copy function. The function of the binder has to be of the form
``fun p1 ... pn -> C (e1, ..., ek)`` with the ``ei`` among the ``pi``;
otherwise no entry is added to the context. The variables that are not bound
by the data being copied have no rule: add one, such as
``term.copy x x ==> ...``, for the ones that occur in the data, as the program
of the example with two binders below does.

For a datum ``l`` whose context is the type ``lctx``, the generated code is
made of:

- ``l``, the conversion (the name of the type);
- ``in_ctx_for_l``, a ``ContextualConversion.ctx_readback`` building a context
  rich enough to read back ``l``, to be passed to ``ContextualPred``;
- ``ctx_for_l``, a class type with one method per context type (here
  ``lctx : lctx Elpi.API.PPX.ctx_field``) that inherits ``Elpi.API.PPX.ctx``,
  the type of the context received by the OCaml function of the builtin.


A datum with several kinds of binders
---------------------------------------

A single type can have binders for variables of different Elpi types, each
kind of variable having its own context type. The context of the datum is then
the merge of all of them: by default the list of the context types mentioned
by its ``[@elpi.binder]`` and ``[@elpi.var]`` attributes, and the object
received by a builtin has one method per context type. In the example, ``Lam``
binds a term variable, with context ``tmctx``, and ``TLam`` binds a type
variable, with context ``tyctx``, as in System F. The ``"ty"`` named by
``TLam`` and by the key of ``tyctx`` is the Elpi type of the bound variables,
and it has to be declared (here with ``LPCode "data ty."``); the Elpi type of
the term variables is the type ``term`` being derived:

.. literalinclude:: ../../ppx_elpi/tests/test_two_binders.ml
   :language: ocaml
   :start-at: type tmctx
   :end-before: let program =

The deep copy of ``term`` goes under both kinds of binders, adding the entry of
the bound variable to the context:

.. literalinclude:: ../../ppx_elpi/tests/test_two_binders.expected.elpi
   :language: elpi
   :start-at: func term.copy
   :end-at: term.copy (tlam

The Elpi program calling the builtin, with an entry for each kind of bound
variable in scope, is:

.. literalinclude:: ../../ppx_elpi/tests/test_two_binders.expected.elpi
   :language: elpi
   :start-at: main :-
   :end-at: print {


.. _ppx-compose-ctx:

Several data types under different contexts
---------------------------------------------

A ``ContextualPred`` has a single context. A predicate taking in input data of types
``t1`` and ``t2`` that live under different contexts needs one rich enough
for both, and none of the ``in_ctx_for_t1``, ``in_ctx_for_t2`` values
generated for the two types is. The structure item

.. literalinclude:: ../../ppx_elpi/tests/test_compose_contextual.ml
   :language: ocaml
   :start-at: [%%elpi.compose_ctx
   :end-at: [%%elpi.compose_ctx

builds it, once ``t1`` and ``t2`` have been derived (each one with its own
context type, here ``c1`` and ``c2``). It defines:

- the class ``ctx_for_both``, which inherits ``ctx_for_t1`` and
  ``ctx_for_t2``, hence has the methods of all the context types involved
  (``c1`` and ``c2``);
- the value ``in_ctx_for_both``, of type
  ``(ctx_for_both, 'csts) ContextualConversion.ctx_readback``, which reads back
  the context of ``t1``, then the one of ``t2``, and builds the object.

The list of types must contain at least one type and the types are read back
in the order they are listed. A context shared by several of them is read back
once for each, with the same result.

The builtin below takes a ``t1`` and a ``t2``, each one under its own context.
It declares ``in_ctx_for_both`` as its context and reads the entries of both
contexts from the object it receives (``c#c1`` and ``c#c2``):

.. literalinclude:: ../../ppx_elpi/tests/test_compose_contextual.ml
   :language: ocaml
   :start-at: (* The context in which both
   :end-before: let builtin =

The Elpi declarations generated for the example, including the signature of
the builtin, are:

.. literalinclude:: ../../ppx_elpi/tests/test_compose_contextual.expected.elpi
   :language: elpi
   :end-before: main :-


.. _ppx-variant:

Constructors with the same name
---------------------------------

Two constructors with the same name, in two different types, are two different
overloads of the same global symbol, and the type tells which one is meant. To
let them coexist give each one its own *variant* with ``[@elpi.variant n]``:

.. literalinclude:: ../../ppx_elpi/tests/test_variant.ml
   :language: ocaml
   :start-after: (* Two constructors with the same name in two types, with different variants *)
   :end-before: let () = Ppx_tests_lib

The declarations generated for it carry the variant, and both ``a`` are used
in the same program:

.. literalinclude:: ../../ppx_elpi/tests/test_variant.expected.elpi
   :language: elpi

Deriving directives
---------------------

``[@@deriving elpi]``
  Derive a ``ContextualConversion.t`` for the types of the (possibly mutually
  recursive) block. The conversion is named like the type.

``[@@deriving elpi { context = [ty1; ...; tyn] }]``
  The types describing the context under which the datum lives, in the order
  in which they are read back. The default is the list of the types mentioned
  in ``[@elpi.binder]`` and ``[@elpi.var]``, in no specified order.

``[@@deriving elpi { declaration = l }]``
  Also add to ``l`` (an ``Elpi.API.PPX.declaration``) the ``MLDataC``
  declarations of the derived types, each one followed by the ``LPCode`` of its
  deep copy function; see the first example.



Attributes
------------

On a type declaration:

``[@@elpi.pp f]``
  ``f`` (mandatory) is the code of the pretty printer of the type, of the type
  ``ppx_deriving.show`` would produce.

``[@@elpi.type_code "name" "code"]``
  ``name`` (mandatory) is a string, the name of the type in Elpi; the default
  is the name of the OCaml type in lowercase with ``_`` replaced by ``-``.
  ``code`` (optional) is a string used as the Elpi kind declaration of the
  type, instead of the generated one.

``[@@elpi.type_doc s]``
  ``s`` (mandatory) is a string, a comment printed before the declaration of
  the type. There is none by default.

``[@@elpi.default_constructor_readback f]``
  ``f`` (mandatory) is a function of type
  ``ContextualConversion.(readback -> readback)``, used when the term is none
  of the constructors (variants and records only). Its argument is the default
  behavior, a runtime type error. It can be used to read back flexible terms,
  in addition to the regular constructors.

``[@@elpi.index (module M)]``
  ``M`` (mandatory) is a module with an ``OrderedType`` and a ``show``, used
  to instantiate the functor ``Elpi.Utils.Map.Make``. In a type carrying it,
  each constructor must have exactly one field marked ``[@elpi.key]``, and
  that field must have type ``M.t``.

``[@@elpi.opaque e]``
  ``e`` (mandatory) is an ``Elpi.API.OpaqueData.declaration``. It is required
  for opaque types.

On a constructor:

``[@elpi.var ctx to_key]``
  The constructor is a bound variable. ``ctx`` (mandatory) is the context in
  which the variable is bound; ``to_key`` (optional) is a function from the
  constructor arguments to the value that is the ``[@elpi.key]`` of the entry
  in ``ctx``.

``[@elpi.skip]``
  The constructor is not exposed to Elpi.

``[@elpi.variant n]``
  The variant of the global symbol of the constructor. ``n`` (mandatory) is an
  integer literal, at least 1. Constructors with the same name, for example in
  different types, need different variants, and the Elpi declaration is
  ``builtin symb name : ... = "n"``; see :ref:`ppx-variant`.

``[@elpi.embed f]``, ``[@elpi.readback f]``
  Custom embedding (resp. readback) code. ``f`` (mandatory) has type
  ``ContextualConversion.(embedding -> embedding)`` (resp.
  ``(readback -> readback)``), and its argument is the function the ppx would
  have generated. To override the default only in some cases, call it in the
  other ones.

``[@elpi.code name code]``
  A custom Elpi declaration. ``name`` (mandatory) is a string, the name of the
  constructor in Elpi; the default is the name of the OCaml constructor in
  lowercase with ``_`` replaced by ``-``, so ``Foo_BAR`` becomes ``foo-bar``.
  ``code`` (optional) is a string used as the declaration of the constructor,
  the default one being derived from the types of its fields, for example
  ``"type lam (term -> term) -> term. % Lam"``.

``[@elpi.doc s]``
  A custom documentation string ``s`` (mandatory). The default is the name of
  the OCaml constructor.

On a field of a constructor:

``[@elpi.key "ty"]``
  The field is the key of the entry in the context map; it can be any of the
  fields of the constructor. ``ty`` (mandatory) is
  the name of the Elpi type of the variables bound by the context, such as the
  ``"term"`` of ``[@elpi.binder "term" ctx ...]``. A constructor of the
  context is declared as ``builtin func name ty -> field1, ..., fieldN`` on the
  Elpi side.

``[@elpi.binder ty ctx mk_ctx_entry]``
  The field is under one binder. ``ty`` (optional) is the name of the Elpi
  type of the abstraction, the ``XXX`` of ``(XXX -> term)``; the default is the
  name of the type being defined. ``ctx`` (mandatory) is the context in which
  the variable is bound. ``mk_ctx_entry`` (mandatory) is a function taking all
  the other fields and returning an entry of ``ctx``.

The extension ``[%elpi : ty]`` stands for the conversion of ``ty``. It does not
synthesize any code, it composes existing conversions.

The structure item ``[%%elpi.compose_ctx name [ty1; ...; tyn]]`` generates a
context for several data types; see :ref:`ppx-compose-ctx`.

Naming conventions of the generated code
------------------------------------------

For a type ``ty``, ``<ty>`` is the ``ContextualConversion.t`` and ``in_ctx_for_<ty>``
the ``ContextualConversion.ctx_readback``. For a context type ``ctx`` annotated
with ``[@@elpi.index (module M)]``, ``Elpi_<ctx>_Map`` is a module of signature
``Elpi.API.Utils.Map.S``, the result of ``Elpi.API.Utils.Map.Make(M)``.
``ctx_for_<name>`` and ``in_ctx_for_<name>``, generated by
``[%%elpi.compose_ctx name [...]]``, have the same shape as the class and the
``ctx_readback`` generated for a type.

Variables in the generated code are named ``elpi__something``, so that they do
not clash with a variable named ``elpi_something`` or ``something`` in the code
being derived.


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
