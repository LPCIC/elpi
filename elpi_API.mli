(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

(* ************************************************************************* *)
(* *************************** Basic API *********************************** *)
(* ************************************************************************* *)

module Setup : sig
  (* Initializes the parser and the tracing facility *)
  val init : ?silent:bool -> string list -> string -> string list
  val usage : string

  (* Can only be switched before calling any Execute API *)
  val trace : string list -> unit

  (* Override default error functions (they call exit) *)
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
  val program : ?no_pervasives:bool -> string list -> Ast.program
  val goal : string -> Ast.query
  val goal_from_stream : char Stream.t -> Ast.query
end

module Data : sig
  type program
  type query
  type term

  type constraints
  type custom_constraints
  type constraint_store = {
    constraints : constraints;
    custom_constraints : custom_constraints;
  }
  type solution = (string * term) list * constraint_store
end

module Compile : sig

  val program : ?print:[`Yes|`Raw] -> Ast.program list -> Data.program (* XXX *)
  val query : Data.program -> Ast.query -> Data.query

  val static_check : ?extra_checker:string list -> Data.program -> Data.query -> unit

end

module Execute : sig
  type outcome = Success of Data.solution | Failure | NoMoreSteps

  val once : ?max_steps:int -> Data.program -> Data.query -> outcome
  val loop : Data.program -> Data.query -> more:(unit -> bool) -> pp:(float -> outcome -> unit) -> unit
end

module Pp : sig

  val term : Format.formatter -> Data.term -> unit
  val constraints : Format.formatter -> Data.constraints -> unit
  val custom_constraints : Format.formatter -> Data.custom_constraints -> unit

  module Ast : sig
    val program : Format.formatter -> Ast.program -> unit
  end

end

(* ************************************************************************* *)
(* ************************* Extension API ********************************* *)
(* ************************************************************************* *)

module Extend : sig

  (* Data of the host program that is opaque to Elpi *)
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

    val morph1 : 'a cdata -> ('a -> 'a) -> t -> t

    val ty2 : 'a cdata -> t -> t -> bool
    val morph2 : 'a cdata -> ('a -> 'a -> 'a) -> t -> t -> t
    
    val map : 'a cdata -> 'b cdata -> ('a -> 'b) -> t -> t
  end

  module Ast : sig

    type term

    val mkApp : term list -> term
    val mkCon : string -> term
    val mkNil : term
    val mkSeq : term list -> term
    val mkCustom : string -> term
    val mkFloat : float -> term
    val mkInt : int -> term
    val mkString : string -> term
    val mkQuoted : string -> term
    val mkFreshUVar : unit -> term
    val mkFreshName : unit -> term
    val mkLam : string -> term -> term

    val query_of_term : term -> Ast.query
    val term_of_query : Ast.query -> term

  end

  module Data : sig

    type constant = int (* De Bruijn levels *)
    type term =
      (* Pure terms *)
      | Const of constant
      | Lam of term
      | App of constant * term * term list
      (* Clause terms: unif variables used in clauses *)
      | Arg of (*id:*)int * (*argsno:*)int
      | AppArg of (*id*)int * term list
      (* Heap terms: unif variables in the query *)
      | UVar of term_attributed_ref * (*depth:*)int * (*argsno:*)int
      | AppUVar of term_attributed_ref * (*depth:*)int * term list
      (* Misc: $custom predicates, ... *)
      | Custom of constant * term list
      | CData of CData.t
      | Cons of term * term
      | Nil
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
    type constraints = Data.constraints
    type custom_constraints = Data.custom_constraints
    type idx

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
    
      (* Value for unassigned UVar/Arg *)
      val dummy : term
    end
    
  end

  module Compile : sig

    (* One can extend the compiler state in order to implement quotations *)
    module ExtState : sig
      type t
    
      type 'a set = t -> 'a -> t
      type 'a update = t -> ('a -> 'a) -> t
      type 'a get = t -> 'a
      type 'a init = unit -> 'a
    
      val declare_extension :
        string -> 'a init -> ('a get * 'a set * 'a update)
      
    end

    type quotation =
      depth:int -> ExtState.t -> string -> ExtState.t * Data.term
    val set_default_quotation : quotation -> unit
    val register_named_quotation : string -> quotation -> unit

    (* The anti-quotation to lambda Prolog *)
    val lp : quotation

    val is_Arg : ExtState.t -> Data.term -> bool

    (* See elpi_quoted_syntax.elpi *)
    val quote_syntax : Data.program -> Data.query -> Data.term * Data.term

    val term_at : depth:int -> Ast.term -> Data.term

  end


  module CustomPredicate : sig

    exception No_clause
    (* Custom predicates like $print. Must either raise No_clause or succeed
       with the list of new goals *)
    val declare :
    string ->
    (depth:int -> env:Data.term array -> Data.term list -> Data.term list) ->
    unit

    type scheduler = {
      delay :
        [ `Goal | `Constraint ] ->
          goal:Data.term -> on:Data.term_attributed_ref list -> unit;
      print : [ `All | `Constraints ] -> Format.formatter -> unit;
    }
    (* Custom predicates like $constraint. Allowed to change the constraint
     * store *)
    val declare_full :
      string ->
      (depth:int -> env:Data.term array -> scheduler -> Data.custom_constraints -> Data.term list ->
       Data.term list * Data.custom_constraints) ->
    unit

  end

  module CustomConstraint : sig

    type 'a constraint_type

    (* 'a must be purely functional *)
    val declare :
      name:string ->
      pp:(Format.formatter -> 'a -> unit) ->
      empty:(unit -> 'a) ->
        'a constraint_type

    val read : Data.custom_constraints -> 'a constraint_type -> 'a
    (* Allowed to raise No_clause *)
    val update :
      Data.custom_constraints -> 'a constraint_type -> ('a -> 'a) ->
        Data.custom_constraints

  end

  module Utils : sig
    val deref_uv :
      from:int -> to_:int -> ano:int -> Data.term -> Data.term
    val deref_appuv :
      from:int -> to_:int -> args:Data.term list -> Data.term -> Data.term
    val deref_head : depth:int -> Data.term -> Data.term
    val is_flex : depth:int -> Data.term -> Data.term_attributed_ref option
    val list_to_lp_list : Data.term list -> Data.term
    val lp_list_to_list : depth:int -> Data.term -> Data.term list
    (* A regular error *)
    val error : string -> 'a
    (* An invariant is broken, i.e. a bug *)
    val anomaly : string -> 'a
    (* If we type check the program, then these are anomalies *)
    val type_error : string -> 'a
    (* A non fatal warning *)
    val warn : string -> unit

  end
        
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
(*

(* Functions useful to implement custom predicates and evaluable functions *)
val print_delayed : unit -> unit
val print_constraints : unit -> unit



val split_conj : term -> term list

(* val llam_unify : int -> term array -> int -> term -> term -> bool *)
end
*)
