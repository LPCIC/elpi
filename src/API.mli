(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(** This module is the API for clients of the Elpi library. *)

(* ************************************************************************* *)
(* *************************** Basic API *********************************** *)
(* ************************************************************************* *)

(** These APIs are sufficient to parse programs and queries from text, run
    the interpreter and finally print the result *)

module Ast : sig
  type program
  type query

  module Loc : sig
    type t = {
      client_payload : Obj.t option;
      source_name : string;
      source_start: int;
      source_stop: int;
      line: int;
      line_starts_at: int;
    }
    val pp : Format.formatter -> t -> unit
    val show : t -> string
    val equal : t -> t -> bool
    val compare : t -> t -> int

    val initial : ?client_payload:Obj.t -> string -> t
  end

  module Name : sig
    type t
    val pp : Format.formatter -> t -> unit
    val show : t -> string

    module Set : sig
      include Set.S with type elt = t
      val show : t -> string
      val pp : Format.formatter -> t -> unit
     end
     module Map : sig
      include Map.S with type key = t
      val show : (Format.formatter -> 'a -> unit) -> 'a t -> string
      val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
     end

   val from_string : string -> t

   type constant = int
   val is_global : t -> int -> bool
  end 
  module Scope : sig
    type t
    val pp : Format.formatter -> t -> unit
    val show : t -> string
    type language
    val pp_language : Format.formatter -> language -> unit
    val show_language : language -> string

    module Map : Map.S with type key = Name.t * language

  end
  module Opaque : sig
    type t
    val pp : Format.formatter -> t -> unit
    val show : t -> string
  end
  
  module Type : sig
    type t_ =
      | Any
      | Con of Name.t
      | App of Name.t * t * t list
      | Arr of t * t
    and t = { it : t_; loc : Loc.t }
    val pp : Format.formatter -> t -> unit
    val show : t -> string
  end

  module Term : sig
    type t_ =
      | Impl of bool * t * t
      | Const of Scope.t * Name.t
      | Discard
      | Var of Name.t * t list (** unification variable *)
      | App of Scope.t * Name.t * t * t list
      | Lam of (Name.t * Scope.language) option * Type.t option * t
      | Opaque of Opaque.t
      | Cast of t * Type.t
    and t = { it : t_; loc : Loc.t; }
    val pp : Format.formatter -> t -> unit
    val show : t -> string

    (** See {!module:RawData.Constants} to allocate global constants *)
    type constant = Name.constant
    val mkGlobal : loc:Loc.t -> constant -> t
    val mkBound : loc:Loc.t -> language:Scope.language -> Name.t -> t
    val mkAppGlobal : loc:Loc.t -> constant -> t -> t list -> t
    val mkAppBound : loc:Loc.t ->  language:Scope.language -> Name.t -> t -> t list -> t
    val mkVar : loc:Loc.t -> Name.t -> t list -> t
    val mkOpaque : loc:Loc.t -> Opaque.t -> t
    val mkCast : loc:Loc.t -> t -> Type.t -> t
    val mkLam : loc:Loc.t -> (Name.t *  Scope.language) option -> ?ty:Type.t -> t -> t
    val mkDiscard : loc:Loc.t -> t

    (** Handy constructors to build goals *)
    val mkImplication : loc:Loc.t -> t -> t -> t
    val mkPi : loc:Loc.t -> Name.t -> ?ty:Type.t -> t -> t
    val mkConj : loc:Loc.t -> t list -> t
    val mkEq : loc:Loc.t -> t -> t -> t
    val mkNil : loc:Loc.t -> t
    (** if omitted, the loc is the merge of the hd and tl locs, as if
        one wrote (hd :: tl), but not as if one wrote [hd|tl] *)
    val mkCons : ?loc:Loc.t -> t -> t -> t

    val list_to_lp_list : loc:Loc.t -> t list -> t
    val ne_list_to_lp_list : t list -> t
    val lp_list_to_list : t -> t list

    (** See Coq-Elpi's lp:(F x) construct *)
    val apply_elpi_var_from_quotation : t -> t list -> t
    val extend_spill_hyp_from_quotation : t -> t list -> t
    val is_spill_from_quotation : t -> bool
  
  end


end

module Setup : sig

  (* State extensions see {!module:State} *)
  type state_descriptor

  (* Quotation extensions see {!module:Quotations} *)
  type quotations_descriptor

  (* HOAS encoding extensions see {!module:RawData} *)
  type hoas_descriptor

  (* Built-in predicates, see {!module:BuiltIn} *)
  type builtins

  (* Operations avaiable via calc (infix is), see {!module:Calc} *)
  type calc_descriptor

  (* Compilation flags, see {!module:Compile} *)
  type flags
  
  (* Handle to an elpi instance *)
  type elpi

  (** Initialize ELPI.

      [init] must be called before invoking the parser.

      @param flags for the compiler, see {!type:Compile.flags}
      @param builtins the set of built-in predicates, eg {!val:Elpi.Builtin.std_builtins}
      @param file_resolver maps a file name to an absolute path, if not specified the
        options like [-I] or the env variable [TJPATH] serve as resolver. The
        resolver returns the abslute file name
        (possibly adjusting the unit extension). By default it fails.
        See also {!val:Parse.std_resolver}.

      @return a handle [elpi] to an elpi instance equipped with the given
        [builtins] and where accumulate resolves files with the given
        [file_resolver]. *)
  val init :
    ?flags:flags ->
    ?state:state_descriptor ->
    ?quotations:quotations_descriptor ->
    ?hoas:hoas_descriptor ->
    ?calc:calc_descriptor ->
    builtins:builtins list ->
    ?file_resolver:(?cwd:string -> unit:string -> unit -> string) ->
    unit ->
    elpi

  (** Usage string *)
  val usage : string

  (** Set tracing options.
      [trace argv] can be called before {!module:Execute}.
      returns options not known to the trace system.
      *)
  val trace : string list -> string list

  (** Override default runtime error functions (they call exit) *)
  val set_warn : (?loc:Ast.Loc.t -> string -> unit) -> unit
  val set_error : (?loc:Ast.Loc.t -> string -> 'a) -> unit
  val set_anomaly : (?loc:Ast.Loc.t -> string -> 'a) -> unit
  val set_type_error : (?loc:Ast.Loc.t -> string -> 'a) -> unit
  val set_std_formatter : Format.formatter -> unit
  val set_err_formatter : Format.formatter -> unit

end

module Parse : sig

  (** [program file_list] parses a list of files,
      Raises Failure if the file does not exist. *)
  val program : elpi:Setup.elpi ->
    files:string list -> Ast.program
  val program_from : elpi:Setup.elpi ->
    loc:Ast.Loc.t -> Lexing.lexbuf -> Ast.program

  (** [goal file_list] parses the query,
      Raises Failure if the file does not exist.  *)
  val goal : elpi:Setup.elpi ->
    loc:Ast.Loc.t -> text:string -> Ast.query
  val goal_from : elpi:Setup.elpi ->
    loc:Ast.Loc.t -> Lexing.lexbuf -> Ast.query

  (** [resolve f] computes the full path of [f] as the parser would do (also)
      for files recursively accumulated. Raises Failure if the file does not
      exist. *)
  val resolve_file : elpi:Setup.elpi -> ?cwd:string -> unit:string -> unit -> string

  (** [std_resolver cwd paths ()] returns a resolver function that looks in cwd
      and paths (relative to cwd, or absolute) *)
  val std_resolver :
    ?cwd:string -> paths:string list -> unit ->
      (?cwd:string -> unit:string -> unit -> string)

  exception ParseError of Ast.Loc.t * string
end


module Compile : sig

  module StrSet : sig
   include Set.S with type elt = string
   val show : t -> string
   val pp : Format.formatter -> t -> unit
  end

  type flags = {
    (* variables used in conditional compilation, that is :if clauses *)
    defined_variables : StrSet.t;
    (* debug: print compilation units *)
    print_units : bool;
  }
  val default_flags : flags
  val to_setup_flags : flags -> Setup.flags

  type program
  type query
  type executable

  exception CompileError of Ast.Loc.t option * string

  (* basic API: Compile all program files in one go.

     Note:
     - programs are concatened and compiled together, as if their sources
       were glued together
     - unless explicitly delimited via `{` and `}`, shorten directives and
       macros are globally visible
     - the `accumulate` directive inserts `{` and `}` around the accumulated
       code
   *)
  val program : ?flags:flags -> elpi:Setup.elpi -> Ast.program list -> program

  (* separate compilation API: scoped_programs and units are marshalable and
     closed w.r.t. the host application (eg quotations are desugared).

     Note:
     - macros and shorten directives part of a unit are not visible in other
       units
     - macros declared as part of the builtins given to Setup.init are
       visible in all units
     - types, type abbreviations and mode declarations from the  units are
       merged at assembly time
*)
  type scoped_program
  val scope : ?flags:flags -> elpi:Setup.elpi -> Ast.program -> scoped_program
  
  type compilation_unit
  type compilation_unit_signature
  val empty_base : elpi:Setup.elpi -> program
  val unit : ?flags:flags -> elpi:Setup.elpi -> base:program -> ?builtins:Setup.builtins list -> scoped_program -> compilation_unit
  val extend : ?flags:flags -> base:program -> compilation_unit -> program

  (* only adds the types/modes from the compilation unit, not its code *)
  val signature : compilation_unit -> compilation_unit_signature
  val extend_signature : ?flags:flags -> base:program -> compilation_unit_signature -> program

  (* then compile the query *)
  val query : program -> Ast.query -> query
  
  (* finally obtain the executable *)
  val optimize : query -> executable
  
  val total_type_checking_time : query -> float
end

module Data : sig

  module StrMap : sig
   include Map.S with type key = string
   val show : (Format.formatter -> 'a -> unit) -> 'a t -> string
   val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  end

  (* what is assigned to the query variables *)
  type term

  (* goals suspended via the declare_constraint built-in *)
  type constraints

  (* user defined state (not goals) *)
  type state

  (* Pass it to function in the Pp module *)
  type pretty_printer_context

  (* a solution is an assignment map from query variables (name) to terms,
   * plus the goals that were suspended and the user defined constraints *)
  type solution = {
    assignments : term StrMap.t;
    constraints : constraints;
    state : state;
    pp_ctx : pretty_printer_context;
    relocate_assignment_to_runtime : target:Compile.program -> depth:int -> string -> (term, string) Stdlib.Result.t (* uvars are turned into discard *)
  }

  (* Hypothetical context *)
  type hyp
  type hyps = hyp list

end

module Execute : sig

  type outcome = Success of Data.solution | Failure | NoMoreSteps

  (* Returns the first solution, if any, within the optional steps bound.
   * Setting delay_outside_fragment (false by default) results in unification
   * outside the pattern fragment to be delayed (behavior of Teyjus), rather
   * than abort the execution (default behavior) *)
  val once : ?max_steps:int -> ?delay_outside_fragment:bool ->
    Compile.executable -> outcome

  (** Prolog's REPL.
    [pp] is called on all solutions.
    [more] is called to know if another solution has to be searched for. *)
  val loop :
    ?delay_outside_fragment:bool ->
    Compile.executable ->
    more:(unit -> bool) -> pp:(float -> outcome -> unit) -> unit
end

module Pp : sig

  val term : Data.pretty_printer_context -> Format.formatter -> Data.term -> unit
  val constraints : Data.pretty_printer_context -> Format.formatter -> Data.constraints -> unit
  val state : Format.formatter -> Data.state -> unit

  val program : Format.formatter -> Compile.program -> unit
  val goal : Format.formatter -> Compile.query -> unit

  module Ast : sig
    val program : Format.formatter -> Ast.program -> unit
    val query : Format.formatter -> Ast.query -> unit
  end

end

(* ************************************************************************* *)
(* ************************* Extension API ********************************* *)
(* ************************************************************************* *)

(** This API lets one exchange with the host application opaque (primitive)
    data such as integers or strings as well as algebraic data such OCaml's
    ADT. No support for binders or unification variables at this point, see
    the RawData module. *)


(** This module defines what embedding and readback functions are *)
module Conversion : sig

  type ty_ast = TyName of string | TyApp of string * ty_ast * ty_ast list

  type extra_goal = ..
  type extra_goal +=
    | Unify of Data.term * Data.term
  
  type extra_goals = extra_goal list

  type 'a embedding =
    depth:int ->
    Data.state -> 'a -> Data.state * Data.term * extra_goals

  type 'a readback =
    depth:int ->
    Data.state -> Data.term -> Data.state * 'a * extra_goals

  type 'a t = {
    ty : ty_ast;
    pp_doc : Format.formatter -> unit -> unit;
    pp : Format.formatter -> 'a -> unit;
    embed : 'a embedding;   (* 'a -> term *)
    readback : 'a readback; (* term -> 'a *)
  }

  exception TypeErr of ty_ast * int (*depth*) * Data.term (* a type error at data conversion time *)
end

(** This module defines what embedding and readback functions are
    for datatypes that need the context of the program (hypothetical clauses and
    constraints) *)
module ContextualConversion : sig

  type ty_ast = Conversion.ty_ast = TyName of string | TyApp of string * ty_ast * ty_ast list


  type ('a,'hyps,'constraints) embedding =
    depth:int -> 'hyps -> 'constraints ->
    Data.state -> 'a -> Data.state * Data.term * Conversion.extra_goals

  type ('a,'hyps,'constraints) readback =
    depth:int -> 'hyps -> 'constraints ->
    Data.state -> Data.term -> Data.state * 'a * Conversion.extra_goals

  type ('a,'h,'c) t = {
    ty : ty_ast;
    pp_doc : Format.formatter -> unit -> unit;
    pp : Format.formatter -> 'a -> unit;
    embed : ('a,'h,'c) embedding;   (* 'a -> term *)
    readback : ('a,'h,'c) readback; (* term -> 'a *)
  }

  type ('hyps,'constraints) ctx_readback =
    depth:int -> Data.hyps -> Data.constraints ->
    Data.state -> Data.state * 'hyps * 'constraints * Conversion.extra_goals

  val unit_ctx : (unit,unit) ctx_readback
  val raw_ctx : (Data.hyps,Data.constraints) ctx_readback

  (* cast *)
  val (!<) : ('a,unit,unit) t -> 'a Conversion.t

  (* morphisms *)
  val (!>)   : 'a Conversion.t -> ('a,'hyps,'constraints) t
  val (!>>)  : ('a Conversion.t -> 'b Conversion.t) -> ('a,'hyps,'constraints) t -> ('b,'hyps,'constraints) t
  val (!>>>) : ('a Conversion.t -> 'b Conversion.t -> 'c Conversion.t) -> ('a,'hyps,'constraints) t -> ('b,'hyps,'constraints) t -> ('c,'hyps,'constraints) t

end


(** Conversion for Elpi's built-in data types *)
module BuiltInData : sig

  (** See {!module:Elpi.Builtin} for a few more *)
  val int    : int Conversion.t
  val float  : float Conversion.t
  val string : string Conversion.t
  val list   : 'a Conversion.t -> 'a list Conversion.t
  val loc    : Ast.Loc.t Conversion.t

  (* poly "A" is what one would use for, say, [type eq A -> A -> prop] *)
  val poly   : string -> Data.term Conversion.t

  (* like poly "A" but "A" must be a closed term, e.g. no unification variables
     and no variables bound by the program (context) *)
  val closed : string -> (Data.term * int) Conversion.t

  (* any is like poly "X" for X fresh *)
  val any    : Data.term Conversion.t

end

(** Declare data from the host application that is opaque (no syntax), like
    int but not like list or pair *)
module OpaqueData : sig

  type doc = string
  type name = string

  (** The [eq] function is used by unification. Limitation: unification of
   * two cdata cannot alter the constraint store. This can be lifted in the
   * future if there is user request.
   *
   * If the hconsed is true, then the [readback] function is
   * automatically hashcons the data using the [eq] and [hash] functions.
   *)
  type 'a declaration = {
    name : name;
    doc : doc;
    pp : Format.formatter -> 'a -> unit;
    compare : 'a -> 'a -> int;
    hash : 'a -> int;
    hconsed : bool;
    constants : (name * 'a) list; (* global constants of that type, eg "std_in" *)
  }

  val declare : 'a declaration -> 'a Conversion.t

end

(** Declare data from the host application that has syntax, like
    list or pair but not like int. So far there is no support for
    data with binder using this API. The type of each constructor is
    described using a GADT so that the code to build or match the data
    can be given the right type. Example: define the ADT for "option a"
{[
   let option_declaration a = {
     ty = TyApp("option",a.ty,[]);
     doc = "The option type (aka Maybe)";
     pp = (fun fmt -> function
             | None -> Format.fprintf fmt "None"
             | Some x -> Format.fprintf fmt "Some %a" a.pp x);
     constructors = [
      K("none","nothing in this case",
        N,                                                   (* no arguments *)
        B None,                                                   (* builder *)
        M (fun ~ok ~ko -> function None -> ok | _ -> ko ()));     (* matcher *)
      K("some","something in this case",
        A (a,N),                                   (* one argument of type a *)
        B (fun x -> Some x),                                      (* builder *)
        M (fun ~ok ~ko -> function Some x -> ok x | _ -> ko ())); (* matcher *)
     ]
   }

   ]}

    [K] stands for "constructor", [B] for "build", [M] for "match".
    Variants [BS] and [MS] give read/write access to the state.

*)
module AlgebraicData : sig

  type name = string
  type doc = string

  type ('match_stateful_t,'match_t, 't) match_t =
    | M of (
        ok:'match_t ->                   (* cont. to call passing subterms *)
        ko:(unit -> Data.term) ->     (* cont. to move to next constructor *)
        't -> Data.term) (* match 't, pass its subterms to ~ok or call ~ko *)
    | MS of (
        ok:'match_stateful_t ->
        ko:(Data.state -> Data.state * Data.term * Conversion.extra_goals) ->
        't -> Data.state -> Data.state * Data.term * Conversion.extra_goals)

  type ('build_stateful_t,'build_t) build_t =
    | B of 'build_t
    | BS of 'build_stateful_t


  (** GADT for describing the type of the constructor:
      - N is the terminator
      - A(a,...) is an argument of type a (a is a Conversion.t)
      - S stands for self
      - C stands for container
  *)
  type ('stateful_builder,'builder, 'stateful_matcher, 'matcher,  'self, 'hyps,'constraints) constructor_arguments =
    (* No arguments *)
    | N : (Data.state -> Data.state * 'self, 'self, Data.state -> Data.state * Data.term * Conversion.extra_goals, Data.term, 'self, 'hyps,'constraints) constructor_arguments
    (* An argument of type 'a *)
    | A : 'a Conversion.t * ('bs,'b, 'ms,'m, 'self, 'hyps,'constraints) constructor_arguments -> ('a -> 'bs, 'a -> 'b, 'a -> 'ms, 'a -> 'm, 'self, 'hyps,'constraints) constructor_arguments
    (* An argument of type 'a in context 'hyps,'constraints *)
    | CA : ('a,'hyps,'constraints) ContextualConversion.t * ('bs,'b, 'ms,'m, 'self, 'hyps,'constraints) constructor_arguments -> ('a -> 'bs, 'a -> 'b, 'a -> 'ms, 'a -> 'm, 'self, 'hyps,'constraints) constructor_arguments
    (* An argument of type 'self *)
    | S : ('bs,'b, 'ms, 'm, 'self, 'hyps,'constraints) constructor_arguments -> ('self -> 'bs, 'self -> 'b, 'self -> 'ms, 'self -> 'm, 'self, 'hyps,'constraints) constructor_arguments
    (* An argument of type `T 'self` for a constainer `T`, like a `list 'self`.
      `S args` above is a shortcut for `C(fun x -> x, args)` *)
    | C : (('self,'hyps,'constraints) ContextualConversion.t -> ('a,'hyps,'constraints) ContextualConversion.t) * ('bs,'b,'ms,'m,'self, 'hyps,'constraints) constructor_arguments -> ('a -> 'bs, 'a -> 'b, 'a -> 'ms,'a -> 'm, 'self, 'hyps,'constraints) constructor_arguments

  type ('t,'h,'c) constructor =
    K : name * doc *
        ('build_stateful_t,'build_t,'match_stateful_t,'match_t,'t,'h,'c) constructor_arguments *   (* args ty *)
        ('build_stateful_t,'build_t) build_t *
        ('match_stateful_t,'match_t,'t) match_t
      -> ('t,'h,'c) constructor

  type ('t,'h,'c) declaration = {
    ty : Conversion.ty_ast;
    doc : doc;
    pp : Format.formatter -> 't -> unit;
    constructors : ('t,'h,'c) constructor list;
  }

  val declare : ('t,'h,'c) declaration -> ('t,'h,'c) ContextualConversion.t

end

(* Built-in predicates are implemented in ML using the following FFI.
   *
   * The ffi data type uses GADTs to let one describe the type of an OCaml
   * function. Terms passed to the built-in predicate are then checked against
   * and converted to their types before being passed to the OCaml code.
   * The ffi data type is also used to generate the documentation of the
   * built-in (Elpi code with comments).
   *
   * Example: built-in "div" taking two int and returning their division and
   * remainder. {[
   *
   *   Pred("div",
   *        In(int, "N",
   *        In(int, "M",
   *        Out(int, "D",
   *        Out(int, "R",
   *          Easy "division of N by M gives D with reminder R")))),
   *        (fun n m _ _ -> !: (n div m) +! (n mod n)))
   *  ]}
   *
   *   In( type, documentation, ... ) declares an input of a given type.
   *     In the example above both "n" and "m" are declare as input, and
   *     as expected the OCaml code receives two inputs (n and m) of type
   *     int
   *   Out( type, documentation, ...) declares an input/output argument.
   *     The OCaml code receives an "int arg" (and not just an int).
   *     We will detail this later, for now lets ignore that.
   *   Easy( documentation ) just signals that the built-in does not alter the
   *     store of custom constraints
   *
   *   The OCaml code has to produce a tuple of outputs, the convenience
   *   notations "!: x" and "x +! y" should be used to produce, respectively,
   *   the first output and any extra one ("!:" begins the list, "+!" continues
   *   it). In the example two outputs (division and reminder) are produced.
   *
   *   In the ffi declaration above "int" is of type "int data" that is a
   *   record containing functions to inject/eject integers into terms.
   *   The function to eject (of_term) does not return an "int" but an
   *   "int arg"  where "'a arg" can be one of
   *     Data of 'a | Flex of term | Discard
   *   For arguments that are described as In in the ffi, only the first
   *   constructor is allowed (i.e. if the user passes a term that is ejected
   *   as Flex or Discard a (fatal, run-time) type error is raised).
   *   For arguments described as Out all 3 cases are valid.
   *
   *   Now let's go back to the two arguments the OCaml code discards.
   *   They are of type "int arg" as a consequence the OCaml code is
   *   made aware of the user passed. For example
   *     div 4 2 D _
   *   would result in the OCaml code being passed: 4, 2, Flex, Discard.
   *   In such a way the code can decide to not even produce the second
   *   output, since it is not requested (not very useful in this specific
   *   case). The notations "?:" and "+?" are like "!:" and "+!" but their
   *   argument is of type option, so one can output None in response to a
   *   Discard.
   *
   *   The FFI unifies the outputs produces by the OCaml code with the
   *   terms provided by the user. It is always correct to produce all
   *   outputs (and ignore the corresponding arguments in OCaml).
   * *)
module BuiltInPredicate : sig

  exception No_clause (* signals logical Failure, i.e. demands backtrack *)

  type name = string
  type doc = string

  type 'a oarg = Keep | Discard
  type 'a ioarg = private Data of 'a | NoData

  type once

  type ('function_type, 'inernal_outtype_in, 'internal_hyps, 'internal_constraints) ffi =
    (* Arguemnts that are translated independently of the program context *)
    | In    : 't Conversion.t * doc * ('i, 'o,'h,'c) ffi -> ('t -> 'i,'o,'h,'c) ffi
    | Out   : 't Conversion.t * doc * ('i, 'o * 't option,'h,'c) ffi -> ('t oarg -> 'i,'o,'h,'c) ffi
    | InOut : 't ioarg Conversion.t * doc * ('i, 'o * 't option,'h,'c) ffi -> ('t ioarg -> 'i,'o,'h,'c) ffi

    (* Arguemnts that are translated looking at the program context *)
    | CIn    : ('t,'h,'c) ContextualConversion.t * doc * ('i, 'o,'h,'c) ffi -> ('t -> 'i,'o,'h,'c) ffi
    | COut   : ('t,'h,'c) ContextualConversion.t * doc * ('i, 'o * 't option,'h,'c) ffi -> ('t oarg -> 'i,'o,'h,'c) ffi
    | CInOut : ('t ioarg,'h,'c) ContextualConversion.t * doc * ('i, 'o * 't option,'h,'c) ffi -> ('t ioarg -> 'i,'o,'h,'c) ffi

    (* The easy case: all arguments are context independent *)
    | Easy : doc -> (depth:int -> 'o, 'o, unit, unit) ffi

    (* The advanced case: arguments are context dependent, here we provide the
      context readback function *)
    | Read : ('h,'c) ContextualConversion.ctx_readback * doc -> (depth:int -> 'h -> 'c -> Data.state -> 'o, 'o,'h,'c) ffi
    | Full : ('h,'c) ContextualConversion.ctx_readback * doc -> (depth:int -> 'h -> 'c -> Data.state -> Data.state * 'o * Conversion.extra_goals, 'o,'h,'c) ffi
    | FullHO : ('h,'c) ContextualConversion.ctx_readback * doc -> (once:once -> depth:int -> 'h -> 'c -> Data.state -> Data.state * 'o * Conversion.extra_goals, 'o,'h,'c) ffi
    | VariadicIn    : ('h,'c) ContextualConversion.ctx_readback * ('t,'h,'c) ContextualConversion.t * doc -> ('t list -> depth:int -> 'h -> 'c -> Data.state -> Data.state * 'o, 'o,'h,'c) ffi
    | VariadicOut   : ('h,'c) ContextualConversion.ctx_readback * ('t,'h,'c) ContextualConversion.t * doc -> ('t oarg list -> depth:int -> 'h -> 'c -> Data.state -> Data.state * ('o * 't option list option), 'o,'h,'c) ffi
    | VariadicInOut : ('h,'c) ContextualConversion.ctx_readback * ('t ioarg,'h,'c) ContextualConversion.t * doc -> ('t ioarg list -> depth:int -> 'h -> 'c -> Data.state -> Data.state * ('o * 't option list option), 'o,'h,'c) ffi

  type t = Pred : name * ('a,unit,'h,'c) ffi * 'a -> t

  (** Tools for InOut arguments.
   *
   *  InOut arguments need to be equipped with an 'a ioarg Conversion.t.
   *  The ioarg adaptor here maps variables to NoData and anything else to the
   *  to Data of the provided 'a Conversion.t.
   *
   *  If the 'a is an atomic data type, eg int, then things are good.
   *  If the 'a is an algebraic data type then some more work has to be done
   *  in order to have a good implementation, but the type system cannot
   *  enforce it hence this documentation. Let's take the example of int option.
   *  The Conversion.t to be passed is [int ioarg option ioarg Conversion.t],
   *  that is, ioarg should wrap each type constructor. In this way the user
   *  can pass non-ground terms. Eg
   *  given term : X       none       some X              some 3
   *  readback to: NoData  Data None  Data (Some NoData)  Data (Some (Data 3))
   *
   *  Alternatively the data type 'a must be able to represent unification
   *  variables, such as the raw terms, see [ioarg_any] below. It gives NoData
   *  if the user passed _ (Discard) and Data t for any other t including
   *  variables such as X (UnifVar).
   *
   *  An example of an API taking advantage of this feature is
   *    pred typecheck i:term, o:ty, o:diagnostic
   *  that can be used to both check a term is well typed and backtrack if not
   *    typecheck T TY ok
   *  or assert a term is illtyped or to test weather it is illtyped
   *    typecheck T TY (error _), typecheck T TY Diagnostic
   *  The ML code can see in which case we are and for example optimize the
   *  first case by not even generating the error message (since error "message"
   *  would fail to unify with ok anyway) or the second one by not assigning TY.
   *)
  val mkData : 'a -> 'a ioarg
  val ioargC : ('t,'h,'c) ContextualConversion.t -> ('t ioarg,'h,'c) ContextualConversion.t
  val ioarg : 't Conversion.t -> 't ioarg Conversion.t
  val ioargC_flex : ('t,'h,'c) ContextualConversion.t -> ('t ioarg,'h,'c) ContextualConversion.t
  val ioarg_flex : 't Conversion.t -> 't ioarg Conversion.t
  val ioarg_any : Data.term ioarg Conversion.t

  module Notation : sig

    (* Handy notation to construct the value generated by built-in predicates.
      *
      * "!" means the output is there, while "?" that it may not be.
      *
      * "?:" and "!:" begin the sequence of outputs, while "+?" and "+!"
      * continue.
      *
      * Eg  !: 3 +! 4 +? None +? (Some 5)           -->
      *     ((((), Some 3), Some 4), None), Some 5
      *)
    val (?:) : 'a -> unit * 'a
    val (!:) : 'a -> unit * 'a option
    val (+?) : 'a -> 'b -> 'a * 'b
    val (+!) : 'a -> 'b -> 'a * 'b option

  end

  (** Adaptors for standard HO functions *)
  module HOAdaptors : sig

    type 'a pred1
    type ('a,'b) pred2
    type ('a) pred2a
    type ('a,'b,'c) pred3
    type ('a,'b) pred3a

    val pred1 : 'a Conversion.t -> 'a pred1 Conversion.t
    val pred2 : 'a Conversion.t -> 'b Conversion.t -> ('a,'b) pred2 Conversion.t
    val pred3 : 'a Conversion.t -> 'b Conversion.t -> 'c Conversion.t -> ('a,'b,'c) pred3 Conversion.t
    val pred2a : 'a Conversion.t -> string -> ('a) pred2a Conversion.t
    val pred3a : 'a Conversion.t -> 'b Conversion.t -> string -> ('a,'b) pred3a Conversion.t

    val filter1 :
      once:once -> depth:int ->
      filter:(('a -> bool) -> 's -> 't) ->
      'a pred1 ->
      's ->
      Data.state ->
      Data.state * 't * Conversion.extra_goals

    val filter2 :
      once:once -> depth:int ->
      filter:(('a -> 'b -> bool) -> 's -> 't) ->
      ('a,'b) pred2 ->
      's ->
      Data.state ->
      Data.state * 't * Conversion.extra_goals

    val map1 :
      once:once -> depth:int ->
      map:(('a -> 'c) -> 's -> 't) ->
      ('a,'c) pred2 ->
      's ->
      Data.state ->
      Data.state * 't * Conversion.extra_goals

    val map2 :
      once:once -> depth:int ->
      map:(('a -> 'b -> 'c) -> 's -> 't) ->
      ('a,'b,'c) pred3 ->
      's ->
      Data.state ->
      Data.state * 't * Conversion.extra_goals

    val fold1 :
      once:once -> depth:int ->
      fold:(('a -> Data.term -> Data.term) -> 's -> Data.term -> Data.term) ->
      ('a) pred2a ->
      's ->
      Data.term ->
      Data.state ->
      Data.state * Data.term * Conversion.extra_goals

    val fold2 :
      once:once -> depth:int ->
      fold:(('a -> 'b -> Data.term -> Data.term) -> 's -> Data.term -> Data.term) ->
      ('a,'b) pred3a ->
      's ->
      Data.term ->
      Data.state ->
      Data.state * Data.term * Conversion.extra_goals

  end

end

(** Setup.init takes a list of declarations of data types and predicates,
    plus some doc and eventually some Elpi code. All this constitutes the
    "prelude", that is what is avaiable to an Elpi program *)
module BuiltIn : sig

  (** Where to print the documentation. For the running example DocAbove
    * generates
    *   % [div N M D R] division of N by M gives D with reminder R
    *   pred div i:int, i:int, o:int, o:int.
    * while DocNext generates
    *   pred div % division of N by M gives D with reminder R
    *    i:int, % N
    *    i:int, % M
    *    o:int, % D
    *    o:int. % R
    * The latter format it is useful to give longer doc for each argument. *)
  type doc_spec = DocAbove | DocNext

  (* When an elpi interpreter is set up one can pass a list of
    * declarations that constitute the base environment in which
    * programs run *)
  type declaration =
    (* Real OCaml code *)
    | MLCode of BuiltInPredicate.t * doc_spec
    (* Declaration of an OCaml data *)
    | MLData : 'a Conversion.t -> declaration
    | MLDataC : ('a,'h,'c) ContextualConversion.t -> declaration
    (* Extra doc *)
    | LPDoc  of string
    (* Sometimes you wrap OCaml code in regular predicates in order
      * to implement the desired builtin *)
    | LPCode of string

  (** What is passed to [Setup.init] *)
  val declare :
    file_name:string -> declaration list -> Setup.builtins

  (** Prints in LP syntax the "external" declarations.
    * The file builtin.elpi is generated by calling this API on the
    * declaration list from elpi_builtin.ml *)
  val document_fmt : Format.formatter -> ?calc:Setup.calc_descriptor -> Setup.builtins -> unit
  val document_file : ?header:string  -> ?calc:Setup.calc_descriptor -> Setup.builtins -> unit

end

(* ************************************************************************* *)
(* ********************* Advanced Extension API **************************** *)
(* ************************************************************************* *)

(** This API lets one access the low lever representation of terms in order
    to exchange data with binders and unification variables with the host
    application. It also lets one define quotations and extend the state
    theraded by Elpi with custom data. *)

(** State is a collection of purely functional piece of data carried
   by the interpreter. Such data is kept in sync with the backtracking, i.e.
   changes made in a branch are lost if that branch fails.
   It can be used to both store custom constraints to be manipulated by
   custom solvers, or any other piece of data the host application may
   need to use. *)
module State : sig

  val new_state_descriptor : unit -> Setup.state_descriptor

  (** 'a MUST be purely functional, i.e. backtracking is implemented by using
   * an old binding for 'a.
   * This limitation can be lifted if there is user request. *)
  type 'a component

  val declare :
    name:string ->
    pp:(Format.formatter -> 'a -> unit) ->
    init:(unit -> 'a) ->
    (* run just before the goal is compiled (but after the program is) *)
    start:('a -> 'a) ->
      'a component
  [@@deprecated "Use [declare_component] instead"]

  val declare_component :
    ?descriptor:Setup.state_descriptor ->
    name:string ->
    pp:(Format.formatter -> 'a -> unit) ->
    init:(unit -> 'a) ->
    (* run just before the goal is compiled (but after the program is) *)
    start:('a -> 'a) ->
    unit ->
      'a component
  
  type t = Data.state

  val get : 'a component -> t -> 'a
  val set : 'a component -> t -> 'a -> t

  (** Allowed to raise BuiltInPredicate.No_clause *)
  val update : 'a component -> t -> ('a -> 'a) -> t
  val update_return : 'a component -> t -> ('a -> 'a * 'b) -> t * 'b

end

(** Flexible data is for unification variables. One can use Elpi's unification
    variables to represent the host equivalent, here the API the keep a link
    between the two. *)
module FlexibleData : sig

  (** key for Elpi's flexible data *)
  module Elpi : sig
    type t
    val make : ?name:string -> Data.state -> Data.state * t
    val get : name:string -> Data.state -> t option
    val pp :  Format.formatter -> t -> unit
    val show :  t -> string
    val equal : t -> t -> bool
    val hash : t -> int
    val fresh : unit -> Ast.Name.t
  end

  module type Host = sig
    type t
    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
    val show : t -> string
  end

  module Map : functor(Host : Host) -> sig
    type t

    val empty : t
    val add : Elpi.t -> Host.t -> t -> t

    val remove_elpi : Elpi.t -> t -> t
    val remove_host : Host.t -> t -> t

    val filter : (Host.t -> Elpi.t -> bool) -> t -> t

    (* The eventual body at its depth *)
    val fold : (Host.t -> Elpi.t -> Data.term option -> 'a -> 'a) -> t -> 'a -> 'a

    val elpi   : Host.t -> t -> Elpi.t
    val host : Elpi.t -> t -> Host.t

    val uvmap : t State.component

    val pp : Format.formatter -> t -> unit
    val show : t -> string
  end

  module type Show = sig
    type t
    val pp : Format.formatter -> t -> unit
    val show : t -> string
  end

   (** Example from Hol-light + elpi:
{[

     module UV2STV = FlexibleData.Map(struct
        type t = int
        let compare x y = x - y
        let pp fmt i = Format.fprintf fmt "%d" i
        let show = string_of_int
      end)

      let stv = ref 0
      let incr_get r = incr r; !r

      let record k state =
        State.update_return UV2STV.uvmap state (fun m ->
          try m, Stv (UV2STV.host k m)
          with Not_found ->
            let j = incr_get stv in
            UV2STV.add k j m, Stv j)

      (* The constructor name "uvar" is special and has to be used with the
         following Conversion.t *)

      let hol_pretype = AlgebraicData.declare {
        ty = TyName "pretype";
        doc = "The algebraic data type of pretypes";
        pp = (fun fmt t -> ...);
        constructors = [
          ...
          K("uvar","",A(uvar,N),
             BS (fun (k,_) state -> record k state),
             M (fun ~ok ~ko _ -> ko ()))
        ]
      }

    ]}

    In this way an Elpi term containig a variable [X] twice gets read back
    using [Stv i] for the same [i].

  *)

  val uvar : (Elpi.t * Data.term list) Conversion.t
end

(** Low level module for OpaqueData *)
module RawOpaqueData : sig

  type name = string
  type doc = string

  type t = Ast.Opaque.t

 (** If the data_hconsed is true, then the [cin] function below will
     automatically hashcons the data using the [eq] and [hash] functions. *)
  type 'a declaration = 'a OpaqueData.declaration = {
    name : name;
    doc : doc;
    pp : Format.formatter -> 'a -> unit;
    compare : 'a -> 'a -> int;
    hash : 'a -> int;
    hconsed : bool;
    constants : (name * 'a) list; (* global constants of that type, eg "std_in" *)
  }

  type 'a cdata = private {
    cin : 'a -> Data.term;
    cino : 'a -> Ast.Opaque.t;
    isc : t -> bool;
    cout: t -> 'a;
    name : string;
  }

  val declare : 'a declaration -> 'a cdata * 'a Conversion.t

  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val name : t -> string
  val hcons : t -> t

  (* tests if two cdata have the same given type *)
  val ty2 : 'a cdata -> t -> t -> bool
  val morph1 : 'a cdata -> ('a -> 'a) -> t -> Data.term
  val morph2 : 'a cdata -> ('a -> 'a -> 'a) -> t -> t -> Data.term
  val map : 'a cdata -> 'b cdata -> ('a -> 'b) -> t -> Data.term

  (* Raw builtin *)
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

end

module Calc : sig

  type operation_declaration = {
    symbol : string;
    infix : bool; (* used for the doc *)
    args : string list list; (* multiple types for the same symbol *)
    code : Data.term list -> Data.term;
  }

  (** Registering an operation *)
  val register : descriptor:Setup.calc_descriptor -> operation_declaration -> unit

  (** An empty descriptor for registering operations *)
  val new_calc_descriptor : unit -> Setup.calc_descriptor

  (** Standard operations *)
  val default_calc : operation_declaration list

  (** The [calc] and [is] declarations *)
  val calc : BuiltIn.declaration list

  (** for use in other builtins *)
  val eval : depth:int -> State.t -> Data.term -> Data.term

end

  (** This module exposes the low level representation of terms.
   *
   * The data type [term] is opaque and can only be accessed by using the
   * [look] API that exposes a term [view]. The [look] view automatically
   * substitutes assigned unification variables by their value. *)
module RawData : sig

  type constant = Ast.Term.constant
  
  (** De Bruijn levels (not indexes): the distance of the binder from the root.
      starts at 0 and grows for bound variables;
      global constants have negative values. *)

  type builtin
  type term = Data.term
  type view = private
    (* Pure subterms *)
    | Const of int                        (* global constant or a bound var *)
    | Lam of term                         (* lambda abstraction, i.e. x\ *)
    | App of int * term * term list       (* application (at least 1 arg) *)
    (* Optimizations *)
    | Cons of term * term                 (* :: *)
    | Nil                                 (* [] *)
    (* FFI *)
    | Builtin of builtin * term list      (* call to a built-in predicate *)
    | CData of RawOpaqueData.t            (* opaque data *)
    (* Unassigned unification variables *)
    | UnifVar of FlexibleData.Elpi.t * term list

  (** Terms must be inspected after dereferencing their head.
      If the resulting term is UVar then its uvar_body is such that
      get_assignment uvar_body = None *)
  val look : depth:int -> term -> view

  (* to reuse a term that was looked at *)
  val kool : view -> term

  (** Smart constructors *)
  val mkBound : int -> term  (* bound variable, i.e. >= 0 *)
  val mkLam : term -> term
  val mkCons : term -> term -> term
  val mkNil : term
  val mkDiscard : term
  val mkCData : RawOpaqueData.t -> term
  val mkUnifVar : FlexibleData.Elpi.t -> args:term list -> State.t -> term

  (** Lower level smart constructors *)
  val mkGlobal : constant -> term (* global constant, i.e. < 0 *)
  val mkAppGlobal  : constant -> term -> term list -> term
  val mkAppGlobalL : constant -> term list -> term
  val mkAppBound  : int -> term -> term list -> term
  val mkAppBoundL : int -> term list -> term
  
  val mkBuiltin : builtin -> term list -> term

  (** no check, works for globals and bound *)
  val mkConst : int -> term
  val mkApp : int -> term -> term list -> term
  val mkAppMoreArgs : depth:int -> term -> term list -> term
  val isApp : depth:int -> term -> bool 

  val cmp_builtin : builtin -> builtin -> int
  type hyp = {
    hdepth : int;
    hsrc : term
  }
  type hyps = hyp list
  val of_hyp : Data.hyp -> hyp
  val of_hyps : Data.hyp list -> hyps

  type suspended_goal = {
    context : hyps;
    goal : int * term
  }
  val constraints : Data.constraints -> suspended_goal list
  val no_constraints : Data.constraints

  module Constants : sig

    val declare_global_symbol : string -> constant

    val show : constant -> string

    val eqc    : builtin (* = *)
    val orc    : constant (* ; *)
    val andc   : constant (* , *)
    val rimplc : constant (* :- *)
    val pic    : constant (* pi *)
    val sigmac : constant (* sigma *)
    val implc  : constant (* => *)
    val cutc   : builtin (* ! *)

    (* LambdaProlog built-in data types are just instances of CData.
     * The typeabbrev machinery translates [int], [float] and [string]
     * to [ctype "int"], [ctype "float"] and [ctype "string"]. *)
    val ctypec : constant (* ctype *)

    (* Marker for spilling function calls, as in [{ rev L }] *)
    val spillc : constant

    module Map : Map.S with type key = constant
    module Set : Set.S with type elt = constant

  end

  (* This extra_goal can be used as a target for postprocessing *)
  type Conversion.extra_goal +=
  | RawGoal of Data.term

  (* This function is called just before returning from a builtin predicate,
     it has visibility over all extra_goals and can add or remove some.
     It must elaborate any extra_goal specific to the host application to
     either Conversion.Unify or RawData.RawGoal.
     
     Since extension to the data type extra_goal are global to all elpi
     instances, this post-processing function is also global *)
  val set_extra_goals_postprocessing :
    ?descriptor:Setup.hoas_descriptor ->
    (Conversion.extra_goals -> State.t -> State.t * Conversion.extra_goals) -> unit

  val new_hoas_descriptor : unit -> Setup.hoas_descriptor

end

(** This module lets one generate a query by providing a RawData.term directly *)
module RawQuery : sig

  (** with the possibility to update the state in which the query will run *)
  val compile_ast :
    Compile.program -> Ast.query -> (State.t -> State.t) -> Compile.query

  (** generate the query ast term with a function. The resulting term is typed, spilled, etc *)
  val compile_term :
    Compile.program -> (State.t -> State.t * Ast.Term.t) -> Compile.query
  
  (** generate the query term by hand, the result is used as is *)
  val compile_raw_term :
    Compile.program -> (State.t -> State.t * Data.term * Conversion.extra_goals) -> Compile.query

  (** typechecks only if ctx is empty *)
  val term_to_raw_term :
    State.t -> Compile.program ->
    ?ctx:RawData.constant Ast.Scope.Map.t ->
    depth:int -> Ast.Term.t -> State.t * Data.term

  (** raises Not_found *)
  val global_name_to_constant : State.t -> string -> RawData.constant
end

module Quotation : sig

  type quotation = language:Ast.Scope.language -> State.t -> Ast.Loc.t -> string -> Ast.Term.t

  (** The default quotation [{{code}}] *)
  val set_default_quotation : ?descriptor:Setup.quotations_descriptor -> quotation -> unit

  (** Named quotation [{{name:code}}] *)
  val register_named_quotation : ?descriptor:Setup.quotations_descriptor -> name:string -> quotation -> Ast.Scope.language

  (** The anti-quotation to lambda Prolog *)
  val elpi_language : Ast.Scope.language
  val elpi : quotation

  (** Like quotations but for identifiers that begin and end with
   * "`" or "'", e.g. `this` and 'that'. Useful if the object language
   * needs something that looks like a string but with a custom compilation
   * (e.g. CD.string like but with a case insensitive comparison) *)

  val declare_backtick : ?descriptor:Setup.quotations_descriptor -> name:string ->
    quotation -> Ast.Scope.language

  val declare_singlequote : ?descriptor:Setup.quotations_descriptor -> name:string ->
    quotation -> Ast.Scope.language

  val new_quotations_descriptor : unit -> Setup.quotations_descriptor

end

module Utils : sig

  (** A regular error (fatal) *)
  val error : ?loc:Ast.Loc.t ->string -> 'a

  (** An invariant is broken, i.e. a bug *)
  val anomaly : ?loc:Ast.Loc.t ->string -> 'a

  (** A type error (in principle ruled out by [elpi-checker.elpi]) *)
  val type_error : ?loc:Ast.Loc.t ->string -> 'a

  (** A non fatal warning *)
  val warn : ?loc:Ast.Loc.t ->string -> unit

  (** link between OCaml and LP lists. Note that [1,2|X] is not a valid
   * OCaml list! *)
  val list_to_lp_list : Data.term list -> Data.term
  val lp_list_to_list : depth:int -> Data.term -> Data.term list

  (** The body of an assignment, if any (LOW LEVEL).
   * Use [look] and forget about this API since the term you get
   * needs to be moved and/or reduced, and you have no API for this. *)
  val get_assignment : FlexibleData.Elpi.t -> Data.term option

  (** Hackish, in particular the output should be a compiled program *)
  val clause_of_term :
    ?name:string -> ?graft:([`After | `Before | `Replace | `Remove] * string) ->
    depth:int -> Ast.Loc.t -> Data.term -> Ast.program

  (** Hackish *)
  val term_to_raw_term :
    State.t -> Compile.program ->
    ?ctx:RawData.constant Ast.Scope.Map.t ->
    depth:int -> Ast.Term.t -> Data.term

  (** Lifting/restriction/beta (LOW LEVEL, don't use) *)
  val move : from:int -> to_:int -> Data.term -> Data.term
  val beta : depth:int -> Data.term -> Data.term list -> Data.term

  (** readback/embed on lists *)
  val map_acc :
    (State.t -> 't -> State.t * 'a * Conversion.extra_goals) ->
    State.t -> 't list -> State.t * 'a list * Conversion.extra_goals

  module type Show = sig
    type t
    val pp : Format.formatter -> t -> unit
    val show : t -> string
  end

  module type Show1 = sig
    type 'a t
    val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
    val show : (Format.formatter -> 'a -> unit) -> 'a t -> string
  end

  module Map : sig
    module type S = sig
      include Map.S
      include Show1 with type 'a t := 'a t
      val pp_key : Format.formatter -> key -> unit
      val show_key : key -> string
    end

    module type OrderedType = sig
      include Map.OrderedType
      include Show with type t := t
    end

    module Make (Ord : OrderedType) : S with type key = Ord.t

  end

  module Set : sig

    module type S = sig
      include Set.S
      include Show with type t := t
    end

    module type OrderedType = sig
      include Set.OrderedType
      include Show with type t := t
    end

    module Make (Ord : OrderedType) : S with type elt = Ord.t

  end

  module IntSet : Set.S with type elt = int
  module LocSet : Set.S with type elt = Ast.Loc.t

end

module RawPp : sig
  (** If the term is under [depth] binders this is the function that has to be
   * called in order to print the term correct. WARNING: as of today printing
   * an open term (i.e. containing unification variables) in the *wrong* depth
   * can cause the pruning of the unification variable.
   * This behavior shall be cleaned up in the future *)
  val term : (*depth*)int -> Format.formatter -> Data.term -> unit

  val constraints : Format.formatter -> Data.constraints -> unit

  val list : ?max:int -> ?boxed:bool ->
    (Format.formatter -> 'a -> unit) ->
    ?pplastelem:(Format.formatter -> 'a -> unit) -> string ->
      Format.formatter -> 'a list -> unit

  module Debug : sig
    val term : (*depth*)int -> Format.formatter -> Data.term -> unit
    val show_term : Data.term -> string
 end

end

(**/**)
