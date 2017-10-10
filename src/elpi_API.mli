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
    Modules {!module:Extend.CustomPredicate} and
    {!module:Extend.CustomConstraint} let one register custom predicates and
    custom constraints. *)

(* ************************************************************************* *)
(* *************************** Basic API *********************************** *)
(* ************************************************************************* *)


module Setup : sig

  (** Initialize ELPI.
      [init ?silent argv basedir] must be called before invoking the parser.
      [argv] is list of options, see the {!val:usage} string;
      [basedir] current working directory (used to make paths absolute);
      [silent] (default [true]) to avoid printing files being loaded.
      It returns part of [argv] not relevant to ELPI. *)
  val init : ?silent:bool -> string list -> string -> string list

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
end

module Ast : sig
  type program
  type query
end

module Parse : sig
  (** [program file_list] parses a list of files *)
  val program : ?no_pervasives:bool -> string list -> Ast.program
  (** [goal file_list] parses the query *)
  val goal : string -> Ast.query
  val goal_from_stream : char Stream.t -> Ast.query
end

module Data : sig
  type program
  type query
  type term

  type syntactic_constraints
  type custom_constraints
  module StrMap : Map.S with type key = string
  type solution = {
    arg_names : int StrMap.t;
    assignments : term array;
    constraints : syntactic_constraints;
    custom_constraints : custom_constraints;
  }
end

module Compile : sig

  val program : ?allow_undeclared_custom_predicates:bool -> ?print:[`Yes|`Raw] -> Ast.program list -> Data.program (* XXX *)
  val query : Data.program -> Ast.query -> Data.query

  (** Runs [elpi_typechecker.elpi]. Extra static checks can be added, see also
      [elpi_quoted_syntax.elpi] *)
  val static_check : ?extra_checker:string list -> Data.program -> Data.query -> unit

end

module Execute : sig

  type outcome = Success of Data.solution | Failure | NoMoreSteps

  (* Returns the first solution, if any, within the optional step bound *)
  val once : ?max_steps:int -> Data.program -> Data.query -> outcome

  (** Prolog's REPL.
   [pp] is called on all solutions.
    [more] is called to know if another solution has to be searched. *)
  val loop :
    Data.program -> Data.query ->
    more:(unit -> bool) -> pp:(float -> outcome -> unit) -> unit
end

module Pp : sig

  val term : Format.formatter -> Data.term -> unit
  val constraints : Format.formatter -> Data.syntactic_constraints -> unit
  val custom_constraints : Format.formatter -> Data.custom_constraints -> unit

  module Ast : sig
    val program : Format.formatter -> Ast.program -> unit
  end

end

(* ************************************************************************* *)
(* ************************* Extension API ********************************* *)
(* ************************************************************************* *)

module Extend : sig

  (** Data of the host program that is opaque to Elpi *)
  module CData : sig
    type t

    type 'a data_declaration = {
      data_name : string;
      data_pp : Format.formatter -> 'a -> unit;
      data_eq : 'a -> 'a -> bool;
      data_hash : 'a -> int;
    }

    type 'a cdata = { cin : 'a -> t; isc : t -> bool; cout: t -> 'a }

    val declare : 'a data_declaration -> 'a cdata


    val pp : Format.formatter -> t -> unit
    val show : t -> string
    val equal : t -> t -> bool
    val hash : t -> int
    val name : t -> string

    (** tests if two cdata have the same given type *)
    val ty2 : 'a cdata -> t -> t -> bool
    val morph1 : 'a cdata -> ('a -> 'a) -> t -> t
    val morph2 : 'a cdata -> ('a -> 'a -> 'a) -> t -> t -> t
    val map : 'a cdata -> 'b cdata -> ('a -> 'b) -> t -> t
  end

  module Ast : sig

    type term (** name based *)

    (** Follows Prolog's convention (capitals are variables) *)
    val mkCon : string -> term

    val mkApp : term list -> term
    val mkLam : string -> term -> term

    val mkFreshUVar : unit -> term

    (** caveat: [a,b,c] -> mkSeq [a;b;c;mkNil] *)
    val mkNil : term
    val mkSeq : term list -> term

    (** builtin data *)
    val mkFloat : float -> term
    val mkInt : int -> term
    val mkString : string -> term

    (** quotation node *)
    val mkQuoted : string -> term

    val query_of_term : ?loc:Ploc.t -> term -> Ast.query
    val term_of_query : Ast.query -> term

  end

  module Data : sig

    type constant = int (** De Bruijn levels *)
    type term =
      (* Pure terms *)
      | Const of constant (** hashconsed *)
      | Lam of term
      | App of constant * term * term list
      (* Clause terms: unif variables used in clauses *)
      | Arg of (*id:*)int * (*argsno:*)int
      | AppArg of (*id*)int * term list
      (* Heap terms: unif variables in the query *)
      | UVar of term_attributed_ref * (*depth:*)int * (*argsno:*)int
      | AppUVar of term_attributed_ref * (*depth:*)int * term list
      (* Misc: custom predicates, ... *)
      | Custom of constant * term list
      | CData of CData.t
      | Cons of term * term
      | Nil
      | Discard
    and term_attributed_ref = {
      mutable contents : term;
      mutable rest : stuck_goal list;
    }
    and stuck_goal = {
      mutable blockers : term_attributed_ref list;
      kind : stuck_goal_kind;
    }
    and stuck_goal_kind

    val of_term : Data.term -> term

    val oref : term -> term_attributed_ref

    type program = Data.program
    type query = Data.query
    type custom_constraints = Data.custom_constraints
    type solution = Data.solution
    type idx
    type hyps = (int * term) list

    type suspended_goal = {
      context : (int * term) list;
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
    
      type hashconsed_string
      val hashcons : string -> hashconsed_string

      val string : hashconsed_string CData.cdata
      val is_string : CData.t -> bool
      val to_string : CData.t -> string
      val of_string : string -> term
    end

    module Constants :
     sig
      val from_string : string -> term
      val from_stringc : string -> constant
     
      val show : constant -> string
      val of_dbl : constant -> term
    
      val eqc : constant
      val orc : constant
      val andc : constant
      val andc2 : constant
      val rimplc : constant
      val ctypec : constant
      val pic : constant
      val sigmac : constant
      val implc : constant
      val cutc : constant
    
      (* Value for unassigned UVar/Arg *)
      val dummy : term
    end
    
  end

  module Compile : sig

    (** One can extend the compiler state in order to implement quotations *)
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

    type quotation =
      depth:int -> State.t -> string -> State.t * Data.term

    (** The default quotation [{{code}}] *)
    val set_default_quotation : quotation -> unit

    (** Named quotation [{{name:code}}] *)
    val register_named_quotation : string -> quotation -> unit

    (* The anti-quotation to lambda Prolog *)
    val lp : quotation

    val is_Arg : State.t -> Data.term -> bool
    val fresh_Arg :
      State.t -> name_hint:string -> args:Data.term list -> State.t * string * Data.term

    (* See elpi_quoted_syntax.elpi *)
    val quote_syntax : Data.program -> Data.query -> Data.term * Data.term

    val term_at : depth:int -> Ast.term -> Data.term
    
    (* Generate a query starting from a compiled/hand-made term *)
    val query :
      Data.program -> (depth:int -> State.t -> State.t * Data.term) -> Data.query

  end


  module CustomPredicate : sig

    exception No_clause

    (** Custom predicates like print. Must either raise No_clause or succeed
        with the list of new goals *)
    val declare :
      string ->
      (depth:int -> Data.term list -> Data.term list) ->
      unit

    (** Custom predicates allowed to change the constraint
        store *)
    val declare_full :
      string ->
      (depth:int -> Data.hyps -> Data.solution -> Data.term list ->
         Data.term list * Data.custom_constraints) ->
      unit

  end

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
    (** Allowed to raise No_clause *)
    val set : 'a component -> t -> 'a -> t
    val update : 'a component -> t -> ('a -> 'a) -> t
    val update_return : 'a component -> t -> ('a -> 'a * 'b) -> t * 'b

  end

  module Utils : sig
    (** Terms must be inspected after dereferencing (at least) their head *)
    val deref_head : depth:int -> Data.term -> Data.term

    (** If a [term_attributed_ref] points to != Constants.dummy then it
        must be dereferenced *)
    val deref_uv :
      from:int -> to_:int -> ano:int -> Data.term -> Data.term
    val deref_appuv :
      from:int -> to_:int -> args:Data.term list -> Data.term -> Data.term

    (** Lifting *)
    val move : from:int -> to_:int -> Data.term -> Data.term

    val is_flex : depth:int -> Data.term -> Data.term_attributed_ref option

    val list_to_lp_list : Data.term list -> Data.term
    val lp_list_to_list : depth:int -> Data.term -> Data.term list

    (** A regular error *)
    val error : string -> 'a
    (** An invariant is broken, i.e. a bug *)
    val anomaly : string -> 'a
    (** A type error (in principle ruled out by [elpi_typechecker.elpi]) *)
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

    val constraint_ : Format.formatter -> Data.stuck_goal_kind -> unit

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

(* Stuff that should be ported to the API, but is not yet *)
module Temporary : sig
  val pp_prolog : Ast.program -> unit
  val activate_latex_exporter : unit -> unit
end
