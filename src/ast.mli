(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Util

(* Prolog functors *)
module Func : sig
  type t
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val equal : t -> t -> bool
  val truef : t
  val andf : t
  val orf : t
  val implf : t
  val rimplf : t
  val cutf : t
  val pif : t
  val sigmaf : t
  val eqf : t
  val isf : t
  val nilf : t
  val consf : t
  val arrowf : t
  val sequentf : t
  val ctypef : t

  val dummyname : t
  val spillf : t

  val from_string : string -> t

  module Map : Map.S with type key = t
end

module Term : sig

  type t =
   | Const of Func.t
   | App of t * t list
   | Lam of Func.t * t
   | CData of CData.t
   | Quoted of quote
  and quote = { data : string; loc : Loc.t; kind : string option }
  
  val equal : t -> t -> bool
  val pp : Format.formatter -> t -> unit
  val show : t -> string

  exception NotInProlog of Loc.t * string
  
  (* Can raise NotInProlog *)
  val mkApp : Loc.t -> t list -> t
  
  val mkCon : string -> t
  val mkNil : t
  val mkSeq : t list -> t
  val mkQuoted : Loc.t -> string -> t
  val mkFreshUVar : unit -> t
  val mkFreshName : unit -> t
  val mkLam : string -> t -> t
  val mkC : CData.t -> t
end

module Clause : sig
  type attribute =
    | Name of string
    | After of string
    | Before of string
    | If of string
  
  val pp_attribute : Format.formatter -> attribute -> unit
  val show_attribute : attribute -> string

  type ('term,'attributes) t = {
    loc : Loc.t;
    attributes : 'attributes;
    body : 'term;
  }

  val pp :
    (Format.formatter -> 'term -> unit) ->
    (Format.formatter -> 'attribute -> unit) ->
      Format.formatter -> ('term,'attribute) t -> unit
  val show :
    (Format.formatter -> 'term -> unit) ->
    (Format.formatter -> 'attribute -> unit) ->
       ('term,'attribute) t -> string
end

module Chr : sig
  type attribute =
    | Name of string
    | If of string
  
  val pp_attribute : Format.formatter -> attribute -> unit
  val show_attribute : attribute -> string

  type sequent = { eigen : Term.t; context : Term.t; conclusion : Term.t }
  and 'attribute t = {
    to_match : sequent list;
    to_remove : sequent list;
    guard : Term.t option;
    new_goal : sequent option;
    attributes : 'attribute;
    loc : Loc.t;
  }
  
  val create :
    ?to_match: sequent list ->
    ?to_remove: sequent list ->
    ?guard: Term.t ->
    ?new_goal: sequent ->
    attributes: 'attribute ->
    loc:Loc.t ->
    unit -> 'attribute t
  val pp : 
    (Format.formatter -> 'attribute -> unit) ->
       Format.formatter -> 'attribute t -> unit
  val show : 
    (Format.formatter -> 'attribute -> unit) ->
       'attribute t -> string
  
end

module Macro : sig
  type ('name,'term) t = {
     loc : Loc.t;
     name : 'name;
     body : 'term
  }
  
  val pp :
    (Format.formatter -> 'name -> unit) ->
    (Format.formatter -> 'term -> unit) ->
      Format.formatter -> ('name,'term) t -> unit
  val show :
    (Format.formatter -> 'name -> unit) ->
    (Format.formatter -> 'term -> unit) ->
       ('name,'term) t -> string

end

module Type : sig


  type attribute =
    | External
    | Index of int list (* depth *)
  
  val pp_attribute : Format.formatter -> attribute -> unit
  val show_attribute : attribute -> string

  type 'attribute t = {
    loc : Loc.t;
    attributes : 'attribute;
    name : Func.t;
    ty : Term.t;
  }
  
  val pp :
    (Format.formatter -> 'attribute -> unit) ->
      Format.formatter -> 'attribute t -> unit
  val show :
    (Format.formatter -> 'attribute -> unit) ->
       'attribute t -> string

end

module Mode : sig

  type 'name t =
    { name : 'name; args : bool list; loc : Loc.t }

  val pp :
    (Format.formatter -> 'name -> unit) ->
      Format.formatter -> 'name t -> unit
  val show :
    (Format.formatter -> 'name -> unit) ->
       'name t -> string

end

module TypeAbbreviation : sig

  type ('name) t =
    { name : 'name; value : Term.t; nparams : int; loc : Loc.t }

  val pp :
    (Format.formatter -> 'name -> unit) ->
      Format.formatter -> 'name t -> unit
  val show :
    (Format.formatter -> 'name -> unit) ->
       'name t -> string

end

module Program : sig

  type decl =
    (* Blocks *)
    | Begin of Loc.t
    | Namespace of Loc.t * Func.t
    | Constraint of Loc.t * Func.t list
    | Shorten of Loc.t * Func.t * Func.t (* prefix suffix *)
    | End of Loc.t

    | Accumulated of Loc.t * (Digest.t * decl list)

    (* data *)
    | Clause of (Term.t, Clause.attribute list) Clause.t
    | Local of Func.t
    | Mode of Func.t Mode.t list
    | Chr of Chr.attribute list Chr.t
    | Macro of (Func.t, Term.t) Macro.t
    | Type of Type.attribute list Type.t
    | TypeAbbreviation of Func.t TypeAbbreviation.t

  val pp_decl : Format.formatter -> decl -> unit
  val show_decl : decl -> string
  
  val mkLocal : string -> decl
  
  type t = decl list
  
  val pp : Format.formatter -> t -> unit
  val show : t -> string

end

module Goal : sig

  type t = Loc.t * Term.t

  val pp : Format.formatter -> t -> unit
  val show : t -> string

end

(* These are declared here for convenience *)

open CData

val cfloat : float cdata
val cint : int cdata
val cstring : string cdata
val cloc : Loc.t cdata

