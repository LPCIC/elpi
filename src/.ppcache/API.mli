(*22838d7ad556bd020c45b042bfd82112 src/API.mli *)
#1 "src/API.mli"
[@@@ocaml.text " This module is the API for clients of the Elpi library. "]
[@@@ocaml.text
  " These APIs are sufficient to parse programs and queries from text, run\n    the interpreter and finally print the result "]
module Ast :
sig
  type program
  type query
  module Loc :
  sig
    type t =
      {
      source_name: string ;
      source_start: int ;
      source_stop: int ;
      line: int ;
      line_starts_at: int }
    val pp : Format.formatter -> t -> unit
    val show : t -> string
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val initial : string -> t
  end
end
module Setup :
sig
  type builtins
  type flags
  type elpi
  val init :
    ?flags:flags ->
      builtins:builtins list ->
        basedir:string -> string list -> (elpi * string list)[@@ocaml.doc
                                                               " Initialize ELPI.\n      [init] must be called before invoking the parser.\n      [builtins] the set of built-in predicates, eg [Elpi_builtin.std_builtins]\n      [basedir] current working directory (used to make paths absolute);\n      [argv] is list of options, see the {!val:usage} string;\n      It returns part of [argv] not relevant to ELPI and a handle [elpi]\n      to an elpi instance equipped with the given builtins. "]
  val usage : string[@@ocaml.doc " Usage string "]
  val trace : string list -> unit[@@ocaml.doc
                                   " Set tracing options.\n      [trace argv] can be called before {!module:Execute}.\n      [argv] is expected to only contain options relevant for\n      the tracing facility. "]
  val set_warn : (?loc:Ast.Loc.t -> string -> unit) -> unit[@@ocaml.doc
                                                             " Override default runtime error functions (they call exit) "]
  val set_error : (?loc:Ast.Loc.t -> string -> 'a) -> unit
  val set_anomaly : (?loc:Ast.Loc.t -> string -> 'a) -> unit
  val set_type_error : (?loc:Ast.Loc.t -> string -> 'a) -> unit
  val set_std_formatter : Format.formatter -> unit
  val set_err_formatter : Format.formatter -> unit
end
module Parse :
sig
  val program :
    elpi:Setup.elpi ->
      ?print_accumulated_files:bool -> string list -> Ast.program[@@ocaml.doc
                                                                   " [program file_list] parses a list of files,\n      Raises Failure if the file does not exist. "]
  val program_from_stream :
    elpi:Setup.elpi ->
      ?print_accumulated_files:bool ->
        Ast.Loc.t -> char Stream.t -> Ast.program
  val goal : Ast.Loc.t -> string -> Ast.query[@@ocaml.doc
                                               " [goal file_list] parses the query,\n      Raises Failure if the file does not exist.  "]
  val goal_from_stream : Ast.Loc.t -> char Stream.t -> Ast.query
  val resolve_file : string -> string[@@ocaml.doc
                                       " [resolve f] computes the full path of [f] as the parser would do (also)\n      for files recursively accumulated. Raises Failure if the file does not\n      exist. "]
  exception ParseError of Ast.Loc.t * string 
end
module Data :
sig
  module StrMap :
  sig
    include Map.S with type  key =  string
    val show : (Format.formatter -> 'a -> unit) -> 'a t -> string
    val pp :
      (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  end
  type term
  type constraints
  type state
  type pretty_printer_context
  type 'a solution =
    {
    assignments: term StrMap.t ;
    constraints: constraints ;
    state: state ;
    output: 'a ;
    pp_ctx: pretty_printer_context }
  type hyp
  type hyps = hyp list
end
module Compile :
sig
  module StrSet :
  sig
    include Set.S with type  elt =  string
    val show : t -> string
    val pp : Format.formatter -> t -> unit
  end
  type flags =
    {
    defined_variables: StrSet.t ;
    print_passes: bool ;
    print_units: bool }
  val default_flags : flags
  val to_setup_flags : flags -> Setup.flags
  type program
  type 'a query
  type 'a executable
  exception CompileError of Ast.Loc.t option * string 
  val program :
    ?flags:flags -> elpi:Setup.elpi -> Ast.program list -> program
  type compilation_unit
  val unit :
    ?flags:flags -> elpi:Setup.elpi -> Ast.program -> compilation_unit
  val assemble :
    ?flags:flags -> elpi:Setup.elpi -> compilation_unit list -> program
  val extend :
    ?flags:flags -> base:program -> compilation_unit list -> program
  val query : program -> Ast.query -> unit query
  val optimize : 'a query -> 'a executable
  val static_check : checker:program -> 'a query -> bool[@@ocaml.doc
                                                          " Runs a checker. Returns true if no errors were found.\n      See also Builtins.default_checker. "]
end
module Execute :
sig
  type 'a outcome =
    | Success of 'a Data.solution 
    | Failure 
    | NoMoreSteps 
  val once :
    ?max_steps:int ->
      ?delay_outside_fragment:bool -> 'a Compile.executable -> 'a outcome
  val loop :
    ?delay_outside_fragment:bool ->
      'a Compile.executable ->
        more:(unit -> bool) -> pp:(float -> 'a outcome -> unit) -> unit
  [@@ocaml.doc
    " Prolog's REPL.\n    [pp] is called on all solutions.\n    [more] is called to know if another solution has to be searched for. "]
end
module Pp :
sig
  val term :
    Data.pretty_printer_context -> Format.formatter -> Data.term -> unit
  val constraints :
    Data.pretty_printer_context ->
      Format.formatter -> Data.constraints -> unit
  val state : Format.formatter -> Data.state -> unit
  val query : Format.formatter -> 'a Compile.query -> unit
  module Ast : sig val program : Format.formatter -> Ast.program -> unit end
end
[@@@ocaml.text
  " This API lets one exchange with the host application opaque (primitive)\n    data such as integers or strings as well as algebraic data such OCaml's\n    ADT. No support for binders or unification variables at this point, see\n    the RawData module. "]
module Conversion :
sig
  type ty_ast =
    | TyName of string 
    | TyApp of string * ty_ast * ty_ast list 
  type extra_goals = Data.term list
  type 'a embedding =
    depth:int -> Data.state -> 'a -> (Data.state * Data.term * extra_goals)
  type 'a readback =
    depth:int -> Data.state -> Data.term -> (Data.state * 'a * extra_goals)
  type 'a t =
    {
    ty: ty_ast ;
    pp_doc: Format.formatter -> unit -> unit ;
    pp: Format.formatter -> 'a -> unit ;
    embed: 'a embedding ;
    readback: 'a readback }
  exception TypeErr of ty_ast * int * Data.term 
end[@@ocaml.doc
     " This module defines what embedding and readback functions are "]
module ContextualConversion :
sig
  type ty_ast = Conversion.ty_ast =
    | TyName of string 
    | TyApp of string * ty_ast * ty_ast list 
  type ('a, 'hyps, 'constraints) embedding =
    depth:int ->
      'hyps ->
        'constraints ->
          Data.state ->
            'a -> (Data.state * Data.term * Conversion.extra_goals)
  type ('a, 'hyps, 'constraints) readback =
    depth:int ->
      'hyps ->
        'constraints ->
          Data.state ->
            Data.term -> (Data.state * 'a * Conversion.extra_goals)
  type ('a, 'h, 'c) t =
    {
    ty: ty_ast ;
    pp_doc: Format.formatter -> unit -> unit ;
    pp: Format.formatter -> 'a -> unit ;
    embed: ('a, 'h, 'c) embedding ;
    readback: ('a, 'h, 'c) readback }
  type ('hyps, 'constraints) ctx_readback =
    depth:int ->
      Data.hyps ->
        Data.constraints ->
          Data.state ->
            (Data.state * 'hyps * 'constraints * Conversion.extra_goals)
  val unit_ctx : (unit, unit) ctx_readback
  val raw_ctx : (Data.hyps, Data.constraints) ctx_readback
  val (!<) : ('a, unit, unit) t -> 'a Conversion.t
  val (!>) : 'a Conversion.t -> ('a, 'hyps, 'constraints) t
  val (!>>) :
    ('a Conversion.t -> 'b Conversion.t) ->
      ('a, 'hyps, 'constraints) t -> ('b, 'hyps, 'constraints) t
  val (!>>>) :
    ('a Conversion.t -> 'b Conversion.t -> 'c Conversion.t) ->
      ('a, 'hyps, 'constraints) t ->
        ('b, 'hyps, 'constraints) t -> ('c, 'hyps, 'constraints) t
end[@@ocaml.doc
     " This module defines what embedding and readback functions are\n    for datatypes that need the context of the program (hypothetical clauses and\n    constraints) "]
module BuiltInData :
sig
  val int : int Conversion.t[@@ocaml.doc " See Elpi_builtin for a few more "]
  val float : float Conversion.t
  val string : string Conversion.t
  val list : 'a Conversion.t -> 'a list Conversion.t
  val loc : Ast.Loc.t Conversion.t
  val poly : string -> Data.term Conversion.t
  val closed : string -> (Data.term * int) Conversion.t
  val any : Data.term Conversion.t
end[@@ocaml.doc " Conversion for Elpi's built-in data types "]
module OpaqueData :
sig
  type doc = string
  type name = string
  type 'a declaration =
    {
    name: name ;
    doc: doc ;
    pp: Format.formatter -> 'a -> unit ;
    compare: 'a -> 'a -> int ;
    hash: 'a -> int ;
    hconsed: bool ;
    constants: (name * 'a) list }[@@ocaml.doc
                                   " The [eq] function is used by unification. Limitation: unification of\n   * two cdata cannot alter the constraint store. This can be lifted in the\n   * future if there is user request.\n   *\n   * If the hconsed is true, then the [readback] function is\n   * automatically hashcons the data using the [eq] and [hash] functions.\n   "]
  val declare : 'a declaration -> 'a Conversion.t
end[@@ocaml.doc
     " Declare data from the host application that is opaque (no syntax), like\n    int but not like list or pair "]
module AlgebraicData :
sig
  type name = string
  type doc = string
  type ('match_stateful_t, 'match_t, 't) match_t =
    | M of (ok:'match_t -> ko:(unit -> Data.term) -> 't -> Data.term) 
    | MS of
    (ok:'match_stateful_t ->
       ko:(Data.state -> (Data.state * Data.term * Conversion.extra_goals))
         ->
         't ->
           Data.state -> (Data.state * Data.term * Conversion.extra_goals))
    
  type ('build_stateful_t, 'build_t) build_t =
    | B of 'build_t 
    | BS of 'build_stateful_t 
  type ('stateful_builder, 'builder, 'stateful_matcher, 'matcher, 'self,
    'hyps, 'constraints) constructor_arguments =
    | N: (Data.state -> (Data.state * 'self), 'self,
    Data.state -> (Data.state * Data.term * Conversion.extra_goals),
    Data.term, 'self, 'hyps, 'constraints) constructor_arguments 
    | A: 'a Conversion.t * ('bs, 'b, 'ms, 'm, 'self, 'hyps, 'constraints)
    constructor_arguments -> ('a -> 'bs, 'a -> 'b, 'a -> 'ms, 'a -> 'm,
    'self, 'hyps, 'constraints) constructor_arguments 
    | CA: ('a, 'hyps, 'constraints) ContextualConversion.t * ('bs, 'b, 
    'ms, 'm, 'self, 'hyps, 'constraints) constructor_arguments -> ('a -> 'bs,
    'a -> 'b, 'a -> 'ms, 'a -> 'm, 'self, 'hyps, 'constraints)
    constructor_arguments 
    | S: ('bs, 'b, 'ms, 'm, 'self, 'hyps, 'constraints) constructor_arguments
    -> ('self -> 'bs, 'self -> 'b, 'self -> 'ms, 'self -> 'm, 'self, 
    'hyps, 'constraints) constructor_arguments 
    | C:
    (('self, 'hyps, 'constraints) ContextualConversion.t ->
       ('a, 'hyps, 'constraints) ContextualConversion.t)
    * ('bs, 'b, 'ms, 'm, 'self, 'hyps, 'constraints) constructor_arguments ->
    ('a -> 'bs, 'a -> 'b, 'a -> 'ms, 'a -> 'm, 'self, 'hyps, 'constraints)
    constructor_arguments [@@ocaml.doc
                            " GADT for describing the type of the constructor:\n      - N is the terminator\n      - A(a,...) is an argument of type a (a is a Conversion.t)\n      - S stands for self\n      - C stands for container\n  "]
  type ('t, 'h, 'c) constructor =
    | K: name * doc * ('build_stateful_t, 'build_t, 'match_stateful_t,
    'match_t, 't, 'h, 'c) constructor_arguments * ('build_stateful_t,
    'build_t) build_t * ('match_stateful_t, 'match_t, 't) match_t -> (
    't, 'h, 'c) constructor 
  type ('t, 'h, 'c) declaration =
    {
    ty: Conversion.ty_ast ;
    doc: doc ;
    pp: Format.formatter -> 't -> unit ;
    constructors: ('t, 'h, 'c) constructor list }
  val declare :
    ('t, 'h, 'c) declaration -> ('t, 'h, 'c) ContextualConversion.t
end[@@ocaml.doc
     " Declare data from the host application that has syntax, like\n    list or pair but not like int. So far there is no support for\n    data with binder using this API. The type of each constructor is\n    described using a GADT so that the code to build or match the data\n    can be given the right type. Example: define the ADT for \"option a\"\n{[\n   let option_declaration a = {\n     ty = TyApp(\"option\",a.ty,[]);\n     doc = \"The option type (aka Maybe)\";\n     pp = (fun fmt -> function\n             | None -> Format.fprintf fmt \"None\"\n             | Some x -> Format.fprintf fmt \"Some %a\" a.pp x);\n     constructors = [\n      K(\"none\",\"nothing in this case\",\n        N,                                                   (* no arguments *)\n        B None,                                                   (* builder *)\n        M (fun ~ok ~ko -> function None -> ok | _ -> ko ()));     (* matcher *)\n      K(\"some\",\"something in this case\",\n        A (a,N),                                   (* one argument of type a *)\n        B (fun x -> Some x),                                      (* builder *)\n        M (fun ~ok ~ko -> function Some x -> ok x | _ -> ko ())); (* matcher *)\n     ]\n   }\n\n   ]}\n\n    [K] stands for \"constructor\", [B] for \"build\", [M] for \"match\".\n    Variants [BS] and [MS] give read/write access to the state.\n\n"]
module BuiltInPredicate :
sig
  exception No_clause 
  type name = string
  type doc = string
  type 'a oarg =
    | Keep 
    | Discard 
  type 'a ioarg = private
    | Data of 'a 
    | NoData 
  type ('function_type, 'inernal_outtype_in, 'internal_hyps,
    'internal_constraints) ffi =
    | In: 't Conversion.t * doc * ('i, 'o, 'h, 'c) ffi -> ('t -> 'i, 
    'o, 'h, 'c) ffi 
    | Out: 't Conversion.t * doc * ('i, ('o * 't option), 'h, 'c) ffi ->
    ('t oarg -> 'i, 'o, 'h, 'c) ffi 
    | InOut: 't ioarg Conversion.t * doc * ('i, ('o * 't option), 'h, 
    'c) ffi -> ('t ioarg -> 'i, 'o, 'h, 'c) ffi 
    | CIn: ('t, 'h, 'c) ContextualConversion.t * doc * ('i, 'o, 'h, 'c) ffi
    -> ('t -> 'i, 'o, 'h, 'c) ffi 
    | COut: ('t, 'h, 'c) ContextualConversion.t * doc * ('i,
    ('o * 't option), 'h, 'c) ffi -> ('t oarg -> 'i, 'o, 'h, 'c) ffi 
    | CInOut: ('t ioarg, 'h, 'c) ContextualConversion.t * doc * ('i,
    ('o * 't option), 'h, 'c) ffi -> ('t ioarg -> 'i, 'o, 'h, 'c) ffi 
    | Easy: doc -> (depth:int -> 'o, 'o, unit, unit) ffi 
    | Read: ('h, 'c) ContextualConversion.ctx_readback * doc ->
    (depth:int -> 'h -> 'c -> Data.state -> 'o, 'o, 'h, 'c) ffi 
    | Full: ('h, 'c) ContextualConversion.ctx_readback * doc ->
    (depth:int ->
       'h -> 'c -> Data.state -> (Data.state * 'o * Conversion.extra_goals),
    'o, 'h, 'c) ffi 
    | VariadicIn: ('h, 'c) ContextualConversion.ctx_readback * ('t, 'h, 
    'c) ContextualConversion.t * doc ->
    ('t list -> depth:int -> 'h -> 'c -> Data.state -> (Data.state * 'o), 
    'o, 'h, 'c) ffi 
    | VariadicOut: ('h, 'c) ContextualConversion.ctx_readback * ('t, 
    'h, 'c) ContextualConversion.t * doc ->
    ('t oarg list ->
       depth:int ->
         'h ->
           'c -> Data.state -> (Data.state * ('o * 't option list option)),
    'o, 'h, 'c) ffi 
    | VariadicInOut: ('h, 'c) ContextualConversion.ctx_readback * ('t ioarg,
    'h, 'c) ContextualConversion.t * doc ->
    ('t ioarg list ->
       depth:int ->
         'h ->
           'c -> Data.state -> (Data.state * ('o * 't option list option)),
    'o, 'h, 'c) ffi 
  type t =
    | Pred: name * ('a, unit, 'h, 'c) ffi * 'a -> t 
  val mkData : 'a -> 'a ioarg[@@ocaml.doc
                               " Tools for InOut arguments.\n   *\n   *  InOut arguments need to be equipped with an 'a ioarg Conversion.t.\n   *  The ioarg adaptor here maps variables to NoData and anything else to the\n   *  to Data of the provided 'a Conversion.t.\n   *\n   *  If the 'a is an atomic data type, eg int, then things are good.\n   *  If the 'a is an algebraic data type then some more work has to be done\n   *  in order to have a good implementation, but the type system cannot\n   *  enforce it hence this documentation. Let's take the example of int option.\n   *  The Conversion.t to be passed is [int ioarg option ioarg Conversion.t],\n   *  that is, ioarg should wrap each type constructor. In this way the user\n   *  can pass non-ground terms. Eg\n   *  given term : X       none       some X              some 3\n   *  readback to: NoData  Data None  Data (Some NoData)  Data (Some (Data 3))\n   *\n   *  Alternatively the data type 'a must be able to represent unification\n   *  variables, such as the raw terms, see [ioarg_any] below.\n   *\n   *  An example of an API taking advantage of this feature is\n   *    pred typecheck i:term, o:ty, o:diagnostic\n   *  that can be used to both check a term is well typed and backtrack if not\n   *    typecheck T TY ok\n   *  or assert a term is illtyped or to test weather it is illtyped\n   *    typecheck T TY (error _), typecheck T TY Diagnostic\n   *  The ML code can see in which case we are and for example optimize the\n   *  first case by not even generating the error message (since error \"message\"\n   *  would fail to unify with ok anyway) or the second one by not assigning TY.\n   "]
  val ioargC :
    ('t, 'h, 'c) ContextualConversion.t ->
      ('t ioarg, 'h, 'c) ContextualConversion.t
  val ioarg : 't Conversion.t -> 't ioarg Conversion.t
  val ioarg_any : Data.term ioarg Conversion.t
  module Notation :
  sig
    val (?:) : 'a -> (unit * 'a)
    val (!:) : 'a -> (unit * 'a option)
    val (+?) : 'a -> 'b -> ('a * 'b)
    val (+!) : 'a -> 'b -> ('a * 'b option)
  end
end
module BuiltIn :
sig
  type doc_spec =
    | DocAbove 
    | DocNext [@@ocaml.doc
                " Where to print the documentation. For the running example DocAbove\n    * generates\n    *   % [div N M D R] division of N by M gives D with reminder R\n    *   pred div i:int, i:int, o:int, o:int.\n    * while DocNext generates\n    *   pred div % division of N by M gives D with reminder R\n    *    i:int, % N\n    *    i:int, % M\n    *    o:int, % D\n    *    o:int. % R\n    * The latter format it is useful to give longer doc for each argument. "]
  type declaration =
    | MLCode of BuiltInPredicate.t * doc_spec 
    | MLData: 'a Conversion.t -> declaration 
    | MLDataC: ('a, 'h, 'c) ContextualConversion.t -> declaration 
    | LPDoc of string 
    | LPCode of string 
  val declare : file_name:string -> declaration list -> Setup.builtins
  [@@ocaml.doc " What is passed to [Setup.init] "]
  val document_fmt : Format.formatter -> Setup.builtins -> unit[@@ocaml.doc
                                                                 " Prints in LP syntax the \"external\" declarations.\n    * The file builtin.elpi is generated by calling this API on the\n    * declaration list from elpi_builtin.ml "]
  val document_file : ?header:string -> Setup.builtins -> unit
end[@@ocaml.doc
     " Setup.init takes a list of declarations of data types and predicates,\n    plus some doc and eventually some Elpi code. All this constitutes the\n    \"prelude\", that is what is avaiable to an Elpi program "]
module Query :
sig
  type name = string
  type _ arguments =
    | N: unit arguments 
    | D: 'a Conversion.t * 'a * 'x arguments -> 'x arguments 
    | Q: 'a Conversion.t * name * 'x arguments -> ('a * 'x) arguments 
  type 'x t =
    | Query of {
    predicate: name ;
    arguments: 'x arguments } 
  val compile : Compile.program -> Ast.Loc.t -> 'a t -> 'a Compile.query
end[@@ocaml.doc
     " Commodity module to build a simple query\n    and extract the output from the solution found by Elpi.\n\n    Example: \"foo data Output\" where [data] has type [t] ([a] is [t Conversion.t])\n    and [Output] has type [v] ([b] is a [v Conversion.t]) can be described as:\n{[\n\n      let q : (v * unit) t = Query {\n        predicate = \"foo\";\n        arguments = D(a, data,\n                    Q(b, \"Output\",\n                    N))\n      }\n\n   ]}\n\n   Then [compile q] can be used to obtain the compiled query such that the\n   resulting solution has a fied output of type [(v * unit)]. Example:\n{[\n\n     Query.compile q |> Compile.link |> Execute.once |> function\n       | Execute.Success { output } -> output\n       | _ -> ...\n\n   ]} "]
[@@@ocaml.text
  " This API lets one access the low lever representation of terms in order\n    to exchange data with binders and unification variables with the host\n    application. It also lets one define quotations and extend the state\n    theraded by Elpi with custom data. "]
module State :
sig
  type 'a component[@@ocaml.doc
                     " 'a MUST be purely functional, i.e. backtracking is implemented by using\n   * an old binding for 'a.\n   * This limitation can be lifted if there is user request. "]
  val declare :
    name:string ->
      pp:(Format.formatter -> 'a -> unit) ->
        init:(unit -> 'a) -> start:('a -> 'a) -> 'a component
  type t = Data.state
  val get : 'a component -> t -> 'a
  val set : 'a component -> t -> 'a -> t
  val update : 'a component -> t -> ('a -> 'a) -> t[@@ocaml.doc
                                                     " Allowed to raise BuiltInPredicate.No_clause "]
  val update_return : 'a component -> t -> ('a -> ('a * 'b)) -> (t * 'b)
end[@@ocaml.doc
     " State is a collection of purely functional piece of data carried\n   by the interpreter. Such data is kept in sync with the backtracking, i.e.\n   changes made in a branch are lost if that branch fails.\n   It can be used to both store custom constraints to be manipulated by\n   custom solvers, or any other piece of data the host application may\n   need to use. "]
module FlexibleData :
sig
  module Elpi :
  sig
    type t
    val make : ?name:string -> Data.state -> (Data.state * t)
    val get : name:string -> Data.state -> t option
    val pp : Format.formatter -> t -> unit
    val show : t -> string
    val equal : t -> t -> bool
  end[@@ocaml.doc " key for Elpi's flexible data "]
  module type Host  =
    sig
      type t
      val compare : t -> t -> int
      val pp : Format.formatter -> t -> unit
      val show : t -> string
    end
  module Map :
  functor (Host : Host) ->
    sig
      type t
      val empty : t
      val add : Elpi.t -> Host.t -> t -> t
      val remove_elpi : Elpi.t -> t -> t
      val remove_host : Host.t -> t -> t
      val filter : (Host.t -> Elpi.t -> bool) -> t -> t
      val fold :
        (Host.t -> Elpi.t -> Data.term option -> 'a -> 'a) -> t -> 'a -> 'a
      val elpi : Host.t -> t -> Elpi.t
      val host : Elpi.t -> t -> Host.t
      val uvmap : t State.component
      val pp : Format.formatter -> t -> unit
      val show : t -> string
    end
  [@@@ocaml.text
    " Example from Hol-light + elpi:\n{[\n\n     module UV2STV = FlexibleData.Map(struct\n        type t = int\n        let compare x y = x - y\n        let pp fmt i = Format.fprintf fmt \"%d\" i\n        let show = string_of_int\n      end)\n\n      let stv = ref 0\n      let incr_get r = incr r; !r\n\n      let record k state =\n        State.update_return UV2STV.uvmap state (fun m ->\n          try m, Stv (UV2STV.host k m)\n          with Not_found ->\n            let j = incr_get stv in\n            UV2STV.add k j m, Stv j)\n\n      (* The constructor name \"uvar\" is special and has to be used with the\n         following Conversion.t *)\n\n      let hol_pretype = AlgebraicData.declare {\n        ty = TyName \"pretype\";\n        doc = \"The algebraic data type of pretypes\";\n        pp = (fun fmt t -> ...);\n        constructors = [\n          ...\n          K(\"uvar\",\"\",A(uvar,N),\n             BS (fun (k,_) state -> record k state),\n             M (fun ~ok ~ko _ -> ko ()))\n        ]\n      }\n\n    ]}\n\n    In this way an Elpi term containig a variable [X] twice gets read back\n    using [Stv i] for the same [i].\n\n  "]
  val uvar : (Elpi.t * Data.term list) Conversion.t
end[@@ocaml.doc
     " Flexible data is for unification variables. One can use Elpi's unification\n    variables to represent the host equivalent, here the API the keep a link\n    between the two. "]
module RawOpaqueData :
sig
  type name = string
  type doc = string
  type t
  type 'a declaration = 'a OpaqueData.declaration =
    {
    name: name ;
    doc: doc ;
    pp: Format.formatter -> 'a -> unit ;
    compare: 'a -> 'a -> int ;
    hash: 'a -> int ;
    hconsed: bool ;
    constants: (name * 'a) list }[@@ocaml.doc
                                   " If the data_hconsed is true, then the [cin] function below will\n     automatically hashcons the data using the [eq] and [hash] functions. "]
  type 'a cdata = private
    {
    cin: 'a -> Data.term ;
    isc: t -> bool ;
    cout: t -> 'a ;
    name: string }
  val declare : 'a declaration -> ('a cdata * 'a Conversion.t)
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val name : t -> string
  val hcons : t -> t
  val ty2 : 'a cdata -> t -> t -> bool
  val morph1 : 'a cdata -> ('a -> 'a) -> t -> Data.term
  val morph2 : 'a cdata -> ('a -> 'a -> 'a) -> t -> t -> Data.term
  val map : 'a cdata -> 'b cdata -> ('a -> 'b) -> t -> Data.term
  val int : int cdata
  val is_int : t -> bool
  val to_int : t -> int
  val of_int : int -> Data.term
  val float : float cdata
  val is_float : t -> bool
  val to_float : t -> float
  val of_float : float -> Data.term
  val string : string cdata
  val is_string : t -> bool
  val to_string : t -> string
  val of_string : string -> Data.term
  val loc : Ast.Loc.t cdata
  val is_loc : t -> bool
  val to_loc : t -> Ast.Loc.t
  val of_loc : Ast.Loc.t -> Data.term
end[@@ocaml.doc " Low level module for OpaqueData "]
module RawData :
sig
  type constant = int[@@ocaml.doc
                       " De Bruijn levels (not indexes):\n                          the distance of the binder from the root.\n                          Starts at 0 and grows for bound variables;\n                          global constants have negative values. "]
  type builtin[@@ocaml.doc
                " De Bruijn levels (not indexes):\n                          the distance of the binder from the root.\n                          Starts at 0 and grows for bound variables;\n                          global constants have negative values. "]
  type term = Data.term
  type view = private
    | Const of constant 
    | Lam of term 
    | App of constant * term * term list 
    | Cons of term * term 
    | Nil 
    | Builtin of builtin * term list 
    | CData of RawOpaqueData.t 
    | UnifVar of FlexibleData.Elpi.t * term list 
  val look : depth:int -> term -> view[@@ocaml.doc
                                        " Terms must be inspected after dereferencing their head.\n      If the resulting term is UVar then its uvar_body is such that\n      get_assignment uvar_body = None "]
  val kool : view -> term
  val mkBound : constant -> term[@@ocaml.doc " Smart constructors "]
  val mkLam : term -> term
  val mkCons : term -> term -> term
  val mkNil : term
  val mkDiscard : term
  val mkCData : RawOpaqueData.t -> term
  val mkUnifVar : FlexibleData.Elpi.t -> args:term list -> State.t -> term
  val mkGlobal : constant -> term[@@ocaml.doc
                                   " Lower level smart constructors "]
  val mkApp : constant -> term -> term list -> term
  val mkAppL : constant -> term list -> term
  val mkBuiltin : builtin -> term list -> term
  val mkConst : constant -> term
  val cmp_builtin : builtin -> builtin -> int
  type hyp = {
    hdepth: int ;
    hsrc: term }
  type hyps = hyp list
  val of_hyps : Data.hyp list -> hyps
  type suspended_goal = {
    context: hyps ;
    goal: (int * term) }
  val constraints : Data.constraints -> suspended_goal list
  val no_constraints : Data.constraints
  module Constants :
  sig
    val declare_global_symbol : string -> constant
    val show : constant -> string
    val eqc : constant
    val orc : constant
    val andc : constant
    val rimplc : constant
    val pic : constant
    val sigmac : constant
    val implc : constant
    val cutc : constant
    val ctypec : constant
    val spillc : constant
    module Map : Map.S with type  key =  constant
    module Set : Set.S with type  elt =  constant
  end
end[@@ocaml.doc
     " This module exposes the low level representation of terms.\n   *\n   * The data type [term] is opaque and can only be accessed by using the\n   * [look] API that exposes a term [view]. The [look] view automatically\n   * substitutes assigned unification variables by their value. "]
module RawQuery :
sig
  val mk_Arg :
    State.t -> name:string -> args:Data.term list -> (State.t * Data.term)
  val is_Arg : State.t -> Data.term -> bool
  val compile :
    Compile.program ->
      (depth:int -> State.t -> (State.t * (Ast.Loc.t * Data.term))) ->
        unit Compile.query
end[@@ocaml.doc
     " This module lets one generate a query by providing a RawData.term directly "]
module Quotation :
sig
  type quotation =
    depth:int -> State.t -> Ast.Loc.t -> string -> (State.t * Data.term)
  val set_default_quotation : quotation -> unit[@@ocaml.doc
                                                 " The default quotation [{{code}}] "]
  val register_named_quotation : name:string -> quotation -> unit[@@ocaml.doc
                                                                   " Named quotation [{{name:code}}] "]
  val lp : quotation[@@ocaml.doc " The anti-quotation to lambda Prolog "]
  val quote_syntax_runtime :
    State.t -> 'a Compile.query -> (State.t * Data.term list * Data.term)
  [@@ocaml.doc
    " See elpi-quoted_syntax.elpi (EXPERIMENTAL, used by elpi-checker) "]
  val quote_syntax_compiletime :
    State.t -> 'a Compile.query -> (State.t * Data.term list * Data.term)
  val term_at : depth:int -> State.t -> Ast.query -> (State.t * Data.term)
  [@@ocaml.doc
    " To implement the string_to_term built-in (AVOID, makes little sense\n   * if depth is non zero, since bound variables have no name!) "]
  [@@@ocaml.text
    " Like quotations but for identifiers that begin and end with\n   * \"`\" or \"'\", e.g. `this` and 'that'. Useful if the object language\n   * needs something that looks like a string but with a custom compilation\n   * (e.g. CD.string like but with a case insensitive comparison) "]
  val declare_backtick :
    name:string -> (State.t -> string -> (State.t * Data.term)) -> unit
  val declare_singlequote :
    name:string -> (State.t -> string -> (State.t * Data.term)) -> unit
end
module Utils :
sig
  val error : ?loc:Ast.Loc.t -> string -> 'a[@@ocaml.doc
                                              " A regular error (fatal) "]
  val anomaly : ?loc:Ast.Loc.t -> string -> 'a[@@ocaml.doc
                                                " An invariant is broken, i.e. a bug "]
  val type_error : ?loc:Ast.Loc.t -> string -> 'a[@@ocaml.doc
                                                   " A type error (in principle ruled out by [elpi-checker.elpi]) "]
  val warn : ?loc:Ast.Loc.t -> string -> unit[@@ocaml.doc
                                               " A non fatal warning "]
  val list_to_lp_list : Data.term list -> Data.term[@@ocaml.doc
                                                     " link between OCaml and LP lists. Note that [1,2|X] is not a valid\n   * OCaml list! "]
  val lp_list_to_list : depth:int -> Data.term -> Data.term list
  val get_assignment : FlexibleData.Elpi.t -> Data.term option[@@ocaml.doc
                                                                " The body of an assignment, if any (LOW LEVEL).\n   * Use [look] and forget about this API since the term you get\n   * needs to be moved and/or reduced, and you have no API for this. "]
  val clause_of_term :
    ?name:string ->
      ?graft:([ `After  | `Before ] * string) ->
        depth:int -> Ast.Loc.t -> Data.term -> Ast.program[@@ocaml.doc
                                                            " Hackish, in particular the output should be a compiled program "]
  val move : from:int -> to_:int -> Data.term -> Data.term[@@ocaml.doc
                                                            " Lifting/restriction/beta (LOW LEVEL, don't use) "]
  val beta : depth:int -> Data.term -> Data.term list -> Data.term
  val map_acc :
    (State.t -> 't -> (State.t * 'a * Conversion.extra_goals)) ->
      State.t -> 't list -> (State.t * 'a list * Conversion.extra_goals)
  [@@ocaml.doc " readback/embed on lists "]
  module type Show  =
    sig type t val pp : Format.formatter -> t -> unit val show : t -> string
    end
  module type Show1  =
    sig
      type 'a t
      val pp :
        (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
      val show : (Format.formatter -> 'a -> unit) -> 'a t -> string
    end
  module Map :
  sig
    module type S  =
      sig include Map.S include Show1 with type 'a t :=  'a t end
    module type OrderedType  =
      sig include Map.OrderedType include Show with type  t :=  t end
    module Make : functor (Ord : OrderedType) -> S with type  key =  Ord.t
  end
  module Set :
  sig
    module type S  = sig include Set.S include Show with type  t :=  t end
    module type OrderedType  =
      sig include Set.OrderedType include Show with type  t :=  t end
    module Make : functor (Ord : OrderedType) -> S with type  elt =  Ord.t
  end
end
module RawPp :
sig
  val term : int -> Format.formatter -> Data.term -> unit[@@ocaml.doc
                                                           " If the term is under [depth] binders this is the function that has to be\n   * called in order to print the term correct. WARNING: as of today printing\n   * an open term (i.e. containing unification variables) in the *wrong* depth\n   * can cause the pruning of the unification variable.\n   * This behavior shall be cleaned up in the future "]
  val constraints : Format.formatter -> Data.constraints -> unit
  val list :
    ?max:int ->
      ?boxed:bool ->
        (Format.formatter -> 'a -> unit) ->
          ?pplastelem:(Format.formatter -> 'a -> unit) ->
            string -> Format.formatter -> 'a list -> unit
  module Debug :
  sig
    val term : int -> Format.formatter -> Data.term -> unit
    val show_term : Data.term -> string
  end
end
[@@@ocaml.text "/*"]

