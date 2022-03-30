(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util.Util

module Loc = Loc

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
  [@@ deriving show]

  exception NotInProlog of Loc.t * string

  (* Can raise NotInProlog *)
  val mkApp : Loc.t -> t list -> t

  val mkAppF : Loc.t -> Func.t -> t list -> t

  val mkCon : string -> t
  val mkNil : t
  val mkSeq : t list -> t
  val mkQuoted : Loc.t -> string -> t
  val mkFreshUVar : unit -> t
  val mkFreshName : unit -> t
  val mkLam : string -> t -> t
  val mkC : CData.t -> t
end

type raw_attribute =
  | If of string
  | Name of string
  | After of string
  | Before of string
  | External
  | Index of int list
[@@ deriving show]

module Clause : sig

  type ('term,'attributes) t = {
    loc : Loc.t;
    attributes : 'attributes;
    body : 'term;
  }
  [@@ deriving show]

end

module Chr : sig

  type sequent = { eigen : Term.t; context : Term.t; conclusion : Term.t }
  and 'attribute t = {
    to_match : sequent list;
    to_remove : sequent list;
    guard : Term.t option;
    new_goal : sequent option;
    attributes : 'attribute;
    loc : Loc.t;
  }
  [@@ deriving show]

end

module Macro : sig
  type ('name,'term) t = {
     loc : Loc.t;
     name : 'name;
     body : 'term
  }
  [@@ deriving show]

end

module Type : sig

  type 'attribute t = {
    loc : Loc.t;
    attributes : 'attribute;
    name : Func.t;
    ty : Term.t;
  }
  [@@ deriving show]

end

module Mode : sig

  type 'name t =
    { name : 'name; args : bool list; loc : Loc.t }
  [@@ deriving show]

end

module TypeAbbreviation : sig

  type ('name) t =
    { name : 'name; value : Term.t; nparams : int; loc : Loc.t }
  [@@ deriving show]

end

module Program : sig

  type decl =
    (* Blocks *)
    | Begin of Loc.t
    | Namespace of Loc.t * Func.t
    | Constraint of Loc.t * Func.t list
    | Shorten of Loc.t * (Func.t * Func.t) list (* prefix suffix *)
    | End of Loc.t

    | Accumulated of Loc.t * (Digest.t * decl list) list

    (* data *)
    | Clause of (Term.t, raw_attribute list) Clause.t
    | Local of Func.t list
    | Mode of Func.t Mode.t list
    | Chr of raw_attribute list Chr.t
    | Macro of (Func.t, Term.t) Macro.t
    | Type of raw_attribute list Type.t list
    | Pred of raw_attribute list Type.t * Func.t Mode.t
    | TypeAbbreviation of Func.t TypeAbbreviation.t
    | Ignored of Loc.t
  [@@ deriving show]

  val mkLocal : string list -> decl

  type t = decl list
  [@@ deriving show]

end

module Goal : sig

  type t = Loc.t * Term.t
  [@@ deriving show]

end

(* These are declared here for convenience *)

open CData

val cfloat : float cdata
val cint : int cdata
val cstring : string cdata
val cloc : Loc.t cdata

module Structured : sig

type program = {
  macros : (Func.t, Term.t) Macro.t list;
  types : tattribute Type.t list;
  type_abbrevs : Func.t TypeAbbreviation.t list;
  modes : Func.t Mode.t list;
  body : block list;
}
and block =
  | Locals of Func.t list * program
  | Clauses of (Term.t,attribute) Clause.t list
  | Namespace of Func.t * program
  | Shorten of Func.t shorthand list * program
  | Constraints of Func.t list * cattribute Chr.t list * program
and attribute = {
  insertion : insertion option;
  id : string option;
  ifexpr : string option;
}
and insertion = Before of string | After of string
and cattribute = {
  cid : string;
  cifexpr : string option
}
and tattribute =
  | External
  | Index of int list
and 'a shorthand = {
  iloc : Loc.t;
  full_name : 'a;
  short_name : 'a;
}
[@@deriving show]

end
