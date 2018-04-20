(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(** This module is the API for clients of the ELPI library.
    
    The modules {!module:Setup}, {!module:Parse}, {!module:Compile} and
    {!module:Execute} let one run code, and {!module:Pp} print the result.
    Modules {!module:Ast} and {!module:Data} mostly contain opaque data types
    declarations.

    The sub module {!module:Extend} groups the APIs to extend ELPI.
    It provides richer {!module:Ast} and {!module:Data} submodules where the
    data types are made transparent.
    Module {!module:Extend.Compile} lets one register new \{\{quotations\}\}.
    Modules {!module:Extend.BuiltInPredicate} and
    {!module:Extend.CustomConstraint} let one register built-in predicates and
    custom constraints. *)

(* ************************************************************************* *)
(* *************************** Basic API *********************************** *)
(* ************************************************************************* *)


module Setup : sig

  (* Built-in predicates, see {!module:Extend.BuiltInPredicate} *)
  type builtins
  type program_header

  (** Initialize ELPI.
      [init] must be called before invoking the parser.
      [silent] (default [true]) to avoid printing files being loaded.
      [builtins] the set of built-in predicates, eg [Elpi_builtin.std_builtins] 
      [basedir] current working directory (used to make paths absolute);
      [argv] is list of options, see the {!val:usage} string;
      It returns part of [argv] not relevant to ELPI and a [program_header]
      that contains the declaration of builtins. *)
  val init :
    ?silent:bool ->
    builtins:builtins ->
    basedir:string ->
    string list -> program_header * string list

  (** Usage string *)
  val usage : string

  (** Set tracing options.
      [trace argv] can be called before {!module:Execute}.
      [argv] is expected to only contain options relevant for
      the tracing facility. *)
  val trace : string list -> unit

  (** Override default error functions (they call exit) *)
  val set_warn : (string -> unit) -> unit
  val set_error : (string -> 'a) -> unit
  val set_anomaly : (string -> 'a) -> unit
  val set_type_error : (string -> 'a) -> unit
  val set_std_formatter : Format.formatter -> unit
  val set_err_formatter : Format.formatter -> unit
end

module Ast : sig
  type program
  type query
end

module Parse : sig

  (** [program file_list] parses a list of files *)
  val program : string list -> Ast.program
  val program_from_stream : char Stream.t -> Ast.program

  (** [goal file_list] parses the query *)
  val goal : string -> Ast.query
  val goal_from_stream : char Stream.t -> Ast.query

end

module Data : sig
  
  module StrMap : Map.S with type key = string

  (* what is assigned to the query variables *)
  type term

  (* goals suspended via the declare_constraint built-in *)
  type syntactic_constraints

  (* user defined constraints (not goals, eg arithmetic constraints) *)
  type custom_constraints

  (* a solution is an assignment map from query variables (name) to terms,
   * plus the goals that were suspended and the user defined constraints *)
  type solution = {
    assignments : term StrMap.t;
    constraints : syntactic_constraints;
    custom_constraints : custom_constraints;
  }
end

module Compile : sig

  module StrSet : Set.S with type elt = string
  type flags = {
    (* variables used in conditional compilation, that is :if clauses *)
    defined_variables : StrSet.t;
    (* disable check that all built-in must come with a type declaration *)
    allow_untyped_builtin : bool;
  }
  val default_flags : flags

  type program
  type query
  type executable

  (* Warning: this API will change to support separate compilation of
   * Ast.program, esp the [link] one *)

  (* compile all program files *)
  val program : Setup.program_header -> Ast.program list -> program

  (* then compile the query *)
  val query : program -> Ast.query -> query

  (* finally obtain the executable *)
  val link : ?flags:flags -> query -> executable

  (** Runs [elpi-checker.elpi] by default. *)
  val static_check :
    Setup.program_header -> ?checker:Ast.program list -> ?flags:flags ->
      query -> bool

  (** HACK: don't use *)
  val dummy_header : Setup.program_header

end

module Execute : sig

  type outcome = Success of Data.solution | Failure | NoMoreSteps

  (* Returns the first solution, if any, within the optional steps bound *)
  val once : ?max_steps:int -> Compile.executable -> outcome

  (** Prolog's REPL.
    [pp] is called on all solutions.
    [more] is called to know if another solution has to be searched for. *)
  val loop :
    Compile.executable ->
    more:(unit -> bool) -> pp:(float -> outcome -> unit) -> unit
end

module Pp : sig

  val term : Format.formatter -> Data.term -> unit
  val constraints : Format.formatter -> Data.syntactic_constraints -> unit
  val custom_constraints : Format.formatter -> Data.custom_constraints -> unit
  val query : Format.formatter -> Compile.query -> unit

  module Ast : sig
    val program : Format.formatter -> Ast.program -> unit
  end

end

(* ************************************************************************* *)
(* ************************* Extension API ********************************* *)
(* ************************************************************************* *)

module Extend : sig

  (** Data of the host program that is opaque to Elpi. *)
  module CData : sig
    type t

    type 'a data_declaration = {
      data_name : string;
      data_pp : Format.formatter -> 'a -> unit;
      data_eq : 'a -> 'a -> bool;
      data_hash : 'a -> int;
      data_hconsed : bool;
    }

    type 'a cdata = { cin : 'a -> t; isc : t -> bool; cout: t -> 'a }

    val declare : 'a data_declaration -> 'a cdata

    val pp : Format.formatter -> t -> unit
    val show : t -> string
    val equal : t -> t -> bool
    val hash : t -> int
    val name : t -> string
    val hcons : t -> t

    (** tests if two cdata have the same given type *)
    val ty2 : 'a cdata -> t -> t -> bool
    val morph1 : 'a cdata -> ('a -> 'a) -> t -> t
    val morph2 : 'a cdata -> ('a -> 'a -> 'a) -> t -> t -> t
    val map : 'a cdata -> 'b cdata -> ('a -> 'b) -> t -> t
  end

  (* This module exposes the low level representation of terms, and is very
   * hard to use. Arg and AppArg are "stack terms" and should never be used.
   * Note: The Utils module provides deref_head to dereference assigned 
   * UVar or AppUVar nodes: always use "match deref_head ~depth t with ..".
   * Note: The "Const" node is hashconsed, see Constants.of_dbl or
   * Contants.from_string, never build it by hand. *)
  module Data : sig

    type constant = int (** De Bruijn levels (not indexes):
                            the distance of the binder from the root.
                            Starts at 0.  *)
    type uvar_body
    type term =
      (* Pure terms *)
      | Const of constant (** hashconsed *)
      | Lam of term
      | App of constant * term * term list
      (* Clause terms: unif variables used in clauses *)
      | Arg of (*id:*)int * (*argsno:*)int
      | AppArg of (*id*)int * term list
      (* Heap terms: unif variables in the query *)
      | UVar of uvar_body * (*depth:*)int * (*argsno:*)int
      | AppUVar of uvar_body * (*depth:*)int * term list
      (* Misc: built-in predicates, ... *)
      | Builtin of constant * term list
      | CData of CData.t
      | Cons of term * term
      | Nil
      | Discard

    type clause_src = { hdepth : int; hsrc : term }

    val of_term : Data.term -> term

    val fresh_uvar_body : unit -> uvar_body

    type custom_constraints = Data.custom_constraints
    type solution = Data.solution
    type idx
    type hyps = clause_src list

    type suspended_goal = {
      context : hyps;
      goal : int * term
    }
    val constraints : Data.syntactic_constraints -> suspended_goal list

    (** builtin data types *)
    module C : sig
      val int : int CData.cdata
      val is_int : CData.t -> bool
      val to_int : CData.t -> int
      val of_int : int -> term
    
      val float : float CData.cdata
      val is_float : CData.t -> bool
      val to_float : CData.t -> float
      val of_float : float -> term
    
      val string : string CData.cdata
      val is_string : CData.t -> bool
      val to_string : CData.t -> string
      val of_string : string -> term
    end

    module Constants :
     sig
      val from_string : string -> term
      val from_stringc : string -> constant
     
      val show : constant -> string

      (* Hashconses the term "Const i" *)
      val of_dbl : constant -> term
    
      val eqc    : constant (* = *)
      val orc    : constant (* ; *)
      val andc   : constant (* , *)
      val andc2  : constant (* & *)
      val rimplc : constant (* :- *)
      val ctypec : constant (* ctype *)
      val pic    : constant (* pi *)
      val sigmac : constant (* sigma *)
      val implc  : constant (* => *)
      val cutc   : constant (* ! *)
    
      module Map : Map.S with type key = constant
      module Set : Set.S with type elt = constant
    end
    
  end

  (* This module lets one implement quotations. In order to do so one may
   * need to carry some data into the compiler state that can indeed be
   * extended. A piece of compiler state can also be kept and used at runtime,
   * e.g. if it contains some custom constraints, see CustomConstraint *)
  module Compile : sig

    (** One can extend the compiler state in order to pass data between
     *  quotations and anti quotations, eg the context of declared variables *)
    module State : sig
      type t
      type 'a component
    
      val declare :
        name:string -> init:(unit -> 'a) ->
          pp:(Format.formatter -> 'a -> unit) -> 'a component

      val get : 'a component -> t -> 'a
      val set : 'a component -> t -> 'a -> t
      val update : 'a component -> t -> ('a -> 'a) -> t
      val update_return : 'a component -> t -> ('a -> 'a * 'b) -> t * 'b
      
    end

    (* From an unparsed string to a term *)
    type quotation =
      depth:int -> State.t -> string -> State.t * Data.term

    (** The default quotation [{{code}}] *)
    val set_default_quotation : quotation -> unit

    (** Named quotation [{{name:code}}] *)
    val register_named_quotation : name:string -> quotation -> unit

    (* The anti-quotation to lambda Prolog *)
    val lp : quotation

    (* Args are clause parameters (capital letters) *)
    val is_Arg : State.t -> Data.term -> bool
    val fresh_Arg :
      State.t -> name_hint:string -> args:Data.term list ->
        State.t * string * Data.term

    (* See elpi_quoted_syntax.elpi *)
    val quote_syntax : Compile.query -> Data.term list * Data.term

    (* To implement the string_to_term builtin. AVOID *)
    val term_at : depth:int -> Ast.query -> Data.term
    
    (* Generate a query starting from a compiled/hand-made term *)
    val query :
      Compile.program -> (depth:int -> State.t -> State.t * Data.term) ->
        Compile.query

  end


  (* Custom constraints are just a purely functional piece of data carried
   * by the interpreter. Such data is kept in sync with the backtracking, i.e.
   * changes made in a branch are lost if that branch fails.
   * The initial value can be taken from the compiler state, e.g. a quotation
   * may generate some constraints statically *)
  module CustomConstraint : sig
    (** 'a must be purely functional, i.e. backtracking is a no op *)

    type 'a component

    (** The initial value of the constraint can be produced at compilation
     *  time (e.g. by quotations) *)
    type ('a,'b) source =
      | CompilerState of 'b Compile.State.component * ('b -> 'a)
      | Other of (unit -> 'a)

    val declare :
      name:string ->
      pp:(Format.formatter -> 'a -> unit) ->
      init:('a,'b) source ->
        'a component

    type t = Data.custom_constraints

    val get : 'a component -> t -> 'a
    (** Allowed to raise BuiltInPredicate.No_clause *)
    val set : 'a component -> t -> 'a -> t
    val update : 'a component -> t -> ('a -> 'a) -> t
    val update_return : 'a component -> t -> ('a -> 'a * 'b) -> t * 'b

  end

  (* Built-in predicates are implemented in ML using the following FFI.
   *
   * The ffi data type uses GADTs to let one describe the type of an OCaml
   * function. Terms passed to the built-in predicate are the checked against
   * and converted to their types before being passed to the OCaml code.
   * The ffi data type is also used to generate the documentation of the
   * built-in (Elpi code with comments).
   *
   * Example: built-in "div" taking two int and returning their division and
   * remainder.
   *
   *   Pred("div",
   *        In(int, "N", In(int, "M", Out(int, "D", Out(int, "R",
   *          Easy "division of N by M givens D with reminder R")))),
   *        (fun n m _ _ -> !: (n div m) +! (n mod n)))
   *
   *   In( type, documentation, ... ) declares an input of a given type.
   *     in the example above both "n" and "m" are declare as input, and
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
   *   as Flex or Discard a (fatal) type error is raised.
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
   *
   * *)
  module BuiltInPredicate : sig

    exception No_clause (* signals logical Failure, i.e. demands backtrack *)

    type name = string
    type doc = string
    
    type 'a arg = Data of 'a | Flex of Data.term | Discard
    exception TypeErr of Data.term
    
    type 'a data = {
      to_term : 'a -> Data.term;
      of_term : depth:int -> Data.term -> 'a arg;
      ty : string
    }
    
    type ('function_type, 'inernal_outtype_in) ffi =
      | In   : 't data * doc * ('i, 'o) ffi -> ('t -> 'i,'o) ffi
      | Out  : 't data * doc * ('i, 'o * 't option) ffi -> ('t arg -> 'i,'o) ffi
      | Easy : doc -> (depth:int -> 'o, 'o) ffi
      | Full : doc -> (depth:int -> Data.hyps -> Data.solution -> Data.custom_constraints * 'o, 'o) ffi
      | VariadicIn : 't data * doc -> ('t list -> depth:int -> Data.hyps -> Data.solution -> Data.custom_constraints * 'o, 'o) ffi
      | VariadicOut : 't data * doc -> ('t arg list -> depth:int -> Data.hyps -> Data.solution -> Data.custom_constraints * ('o * 't option list option), 'o) ffi
    type t = Pred : name * ('a,unit) ffi * 'a -> t

    type doc_spec = DocAbove | DocNext

    type declaration =
    (* Real OCaml code *)
    | MLCode of t * doc_spec
    (* Extra doc *)
    | LPDoc  of string
    (* Sometimes you wrap OCaml code in regular predicates or similar in order
     * to implement the desired builtin, maybe just temporarily because writing
     * LP code is simpler *)
    | LPCode of string

    val int    : int data
    val float  : float data
    val string : string data
    val list   : 'a data -> 'a list data

    val poly   : string -> Data.term data
    val any    : Data.term data

    val data_of_cdata :
      (* name used for type declarations, eg "int" or "@in_stream" *)
      name:string ->
      (* global constants of that type, eg "std_in" *)
      ?constants:'a Data.Constants.Map.t ->
      'a CData.cdata -> 'a data

    (* Prints in LP syntax the "external" declarations *)
    val document : Format.formatter -> declaration list -> unit

    val builtin_of_declaration : declaration list -> Setup.builtins

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
  end

  (* Like quotations but for `this` and 'that' *)
  module CustomFunctor : sig

    val declare_backtick : name:string ->
      (Compile.State.t -> string -> Compile.State.t * Data.term) -> unit

    val declare_singlequote : name:string ->
      (Compile.State.t -> string -> Compile.State.t * Data.term) -> unit

  end


  module Utils : sig

    (** Terms must be inspected after dereferencing their head.
        If the resulting term is UVar then its uvar_body is such that
        get_assignment uvar_body = None *)
    val deref_head : depth:int -> Data.term -> Data.term

    (** LOW LEVEL: the body of an assignment, if any variable is assigned.
        Use deref_head and forget about this API since the term you get
        needs to be moved and/or reduced, and you have no API for this. *)
    val get_assignment : Data.uvar_body -> Data.term option

    (** Hackish, in particular the output should be a compiled program *)
    val clause_of_term :
      ?name:string -> ?graft:([`After | `Before] * string) ->
      depth:int -> Data.term -> Ast.program

    (** Lifting/restriction *)
    val move : from:int -> to_:int -> Data.term -> Data.term

    val list_to_lp_list : Data.term list -> Data.term
    val lp_list_to_list : depth:int -> Data.term -> Data.term list

    (** A regular error *)
    val error : string -> 'a
    (** An invariant is broken, i.e. a bug *)
    val anomaly : string -> 'a
    (** A type error (in principle ruled out by [elpi-checker.elpi]) *)
    val type_error : string -> 'a
    (** A non fatal warning *)
    val warn : string -> unit

  end
        
  (** TODO: too rough *)
  module Pp : sig

    val term : ?min_prec:int ->
      int -> string list ->
      int -> Data.term array ->
        Format.formatter -> Data.term -> unit

    val list : ?max:int -> ?boxed:bool ->
     (Format.formatter -> 'a -> unit) ->
     ?pplastelem:(Format.formatter -> 'a -> unit) -> string ->
     Format.formatter -> 'a list -> unit

    module Raw : sig
      val term : ?min_prec:int ->
        int -> string list ->
        int -> Data.term array ->
          Format.formatter -> Data.term -> unit
      val show_term : Data.term -> string
   end

  end

end (* Extend *)

(**/**)
