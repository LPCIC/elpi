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
  val propf : t
  val typef : t
  val mainf : t

  val dummyname : t
  val spillf : t

  val is_uvar_name : t -> bool

  val from_string : string -> t

  module Map : Map.S with type key = t
  module Set : Set.S with type elt = t
end

module Mode : sig

  type t = Input | Output
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
  | Untyped
[@@ deriving show]

module TypeExpression : sig

  type 'attribute t_ =
   | TConst of Func.t
   | TApp of Func.t * 'attribute t * 'attribute t list
   | TPred of 'attribute * (Mode.t * 'attribute t) list
   | TArr of 'attribute t * 'attribute t
   and 'a t = { tit : 'a t_; tloc : Loc.t }
   [@@ deriving show, ord]

end

module Term : sig
  type typ = raw_attribute list TypeExpression.t
  [@@ deriving show, ord]
  type t_ =
   | Const of Func.t
   | App of t * t list
   | Lam of Func.t * typ option * t
   | CData of CData.t
   | Quoted of quote
   | Cast of t * typ
   | Parens of t
  and t = { it : t_; loc : Loc.t }
  and quote = { qloc : Loc.t; data : string; kind : string option }
  [@@ deriving show, ord]

  exception NotInProlog of Loc.t * string

  (* Can raise NotInProlog *)
  val mkApp : Loc.t -> t list -> t
  val mkParens : Loc.t -> t -> t
  val mkAppF : Loc.t -> (Loc.t * Func.t) -> t list -> t

  val mkCon : Loc.t -> string -> t
  val mkConst : Loc.t -> Func.t -> t
  val mkNil : Loc.t -> t
  val mkSeq : ?loc:Loc.t -> t list -> t
  val mkQuoted : Loc.t -> int -> string -> t
  val mkFreshUVar : Loc.t -> t
  val mkFreshName : Loc.t -> t
  val mkLam : Loc.t -> string -> typ option -> t -> t
  val mkC : Loc.t -> CData.t -> t
  val mkCast : Loc.t -> t -> typ -> t

end

module Clause : sig

  type ('term,'attributes,'spill) t = {
    loc : Loc.t;
    attributes : 'attributes;
    body : 'term;
    needs_spilling : 'spill;
  }
  [@@ deriving show, ord]

end

module Chr : sig

  type 'term sequent = { eigen : 'term; context : 'term; conclusion : 'term }
  and ('attribute,'term) t = {
    to_match : 'term sequent list;
    to_remove : 'term sequent list;
    guard : 'term option;
    new_goal : 'term sequent option;
    attributes : 'attribute;
    loc : Loc.t;
  }
  [@@ deriving show,ord]

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

  type ('attribute,'inner_attribute) t = {
    loc : Loc.t;
    attributes : 'attribute;
    name : Func.t;
    ty : 'inner_attribute TypeExpression.t;
  }
  [@@deriving show, ord]

end

module TypeAbbreviation : sig

  type 'ty closedTypeexpression = 
    | Lam of Func.t * Loc.t * 'ty closedTypeexpression 
    | Ty of 'ty
  [@@ deriving show, ord]

  type ('name,'ty) t =
    { name : 'name; value : 'ty closedTypeexpression; nparams : int; loc : Loc.t }
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

    | Accumulated of Loc.t * parser_output list

    (* data *)
    | Clause of (Term.t, raw_attribute list, unit) Clause.t
    | Chr of (raw_attribute list,Term.t) Chr.t
    | Macro of (Func.t, Term.t) Macro.t
    | Kind of (raw_attribute list,raw_attribute list) Type.t list
    | Type of (raw_attribute list,raw_attribute list) Type.t list
    | Pred of (raw_attribute list,raw_attribute list) Type.t
    | TypeAbbreviation of (Func.t,raw_attribute list TypeExpression.t) TypeAbbreviation.t
    | Ignored of Loc.t
  and parser_output = { file_name : string; digest : Digest.t; ast : decl list }
  [@@ deriving show]

  type t = decl list
  [@@ deriving show]

end

module Goal : sig

  type t = Term.t
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
  kinds : (unit,unit) Type.t list;
  types : (tattribute,functionality) Type.t list;
  type_abbrevs : (Func.t,functionality TypeExpression.t) TypeAbbreviation.t list;
  body : block list;
}
and ('func,'term) block_constraint = {
   clique : 'func list;
   ctx_filter : 'func list;
   rules : (cattribute,'term) Chr.t list
}
and block =
  | Clauses of (Term.t,attribute,unit) Clause.t list
  | Namespace of Func.t * program
  | Shorten of Func.t shorthand list * program
  | Constraints of (Func.t,Term.t) block_constraint * program
  | Accumulated of program
and attribute = {
  insertion : insertion option;
  id : string option;
  ifexpr : string option;
  typecheck : bool;
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
and tindex = Map | HashMap | DiscriminationTree
and 'a shorthand = {
  iloc : Loc.t;
  full_name : 'a;
  short_name : 'a;
}
and functionality = Function | Relation
and variadic = Variadic | NotVariadic
[@@deriving show, ord]

end
