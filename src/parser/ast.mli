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

  val is_uvar_name : t -> bool

  val from_string : string -> t

  module Map : Map.S with type key = t
end

module Mode : sig

  type mode = Input | Output
  [@@deriving show, ord]

end

type raw_attribute =
  | If of string
  | Name of string
  | After of string
  | Before of string
  | Replace of string
  | Remove of string
  | External
  | Index of int list * string option
  | Functional
[@@ deriving show]

module TypeExpression : sig
  type t =
   | TConst of Func.t
   | TApp of Func.t * t * t list
   | TPred of raw_attribute list * ((Mode.mode * t) list)
   | TArr of t * t
   | TCData of CData.t
  [@@ deriving show, ord]
end

module Term : sig

  type t_ =
   | Const of Func.t
   | App of t * t list
   | Lam of Func.t * t
   | CData of CData.t
   | Quoted of quote
  and t = { it : t_; loc : Loc.t }
  and quote = { qloc : Loc.t; data : string; kind : string option }
  [@@ deriving show, ord]

  exception NotInProlog of Loc.t * string

  (* Can raise NotInProlog *)
  val mkApp : Loc.t -> t list -> t

  val mkAppF : Loc.t -> (Loc.t * Func.t) -> t list -> t

  val mkCon : Loc.t -> string -> t
  val mkConst : Loc.t -> Func.t -> t
  val mkNil : Loc.t -> t
  val mkSeq : Loc.t -> t list -> t
  val mkQuoted : Loc.t -> string -> t
  val mkFreshUVar : Loc.t -> t
  val mkFreshName : Loc.t -> t
  val mkLam : Loc.t -> string -> t -> t
  val mkC : Loc.t -> CData.t -> t

end

(* module ScopedTerm : sig

  type t_ =
   | Global of Func.t
   | Local of Func.t
   | Var of Func.t * t list
   | App of Func.t * t * t list
   | Lam of Func.t * t
   | CData of CData.t
   and t = { it : t; loc : Loc.t }
  [@@ deriving show, ord]
  
end *)

type raw_attribute =
  | If of string
  | Name of string
  | After of string
  | Before of string
  | Replace of string
  | Remove of string
  | External
  | Index of int list * string option
  | Functional
[@@ deriving show]

module Clause : sig

  type ('term,'attributes) t = {
    loc : Loc.t;
    attributes : 'attributes;
    body : 'term;
  }
  [@@ deriving show, ord]

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
    ty : TypeExpression.t;
  }
  [@@ deriving show]

end

module TypeAbbreviation : sig

  type closedTypeexpression = 
    | Lam of Func.t * closedTypeexpression 
    | Ty of TypeExpression.t
  [@@ deriving show, ord]

  type ('name) t =
    { name : 'name; value : closedTypeexpression; nparams : int; loc : Loc.t }
  [@@ deriving show, ord]

end

module Program : sig

  type decl =
    (* Blocks *)
    | Begin of Loc.t
    | Namespace of Loc.t * Func.t
    | Constraint of Loc.t * Func.t list * Func.t list
    | Shorten of Loc.t * (Func.t * Func.t) list (* prefix suffix *)
    | End of Loc.t

    | Accumulated of Loc.t * (Digest.t * decl list) list

    (* data *)
    | Clause of (Term.t, raw_attribute list) Clause.t
    | Local of Func.t list
    | Mode of raw_attribute list Type.t list
    | Chr of raw_attribute list Chr.t
    | Macro of (Func.t, Term.t) Macro.t
    | Type of raw_attribute list Type.t list
    | Pred of raw_attribute list Type.t
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
  modes : tattribute Type.t list;
  functionality : Func.t list;
  body : block list;
}
and block_constraint = {
   clique : Func.t list;
   ctx_filter : Func.t list;
   rules : cattribute Chr.t list
}
and block =
  | Locals of Func.t list * program
  | Clauses of (Term.t,attribute) Clause.t list
  | Namespace of Func.t * program
  | Shorten of Func.t shorthand list * program
  | Constraints of block_constraint * program
and attribute = {
  insertion : insertion option;
  id : string option;
  ifexpr : string option;
}
and insertion = Insert of insertion_place | Replace of string | Remove of string
and insertion_place = Before of string | After of string
and cattribute = {
  cid : string;
  cifexpr : string option
}
and tattribute =
  | External
  | Index of int list * tindex option
  | Functional
and tindex = Map | HashMap | DiscriminationTree
and 'a shorthand = {
  iloc : Loc.t;
  full_name : 'a;
  short_name : 'a;
}
[@@deriving show, ord]

end
