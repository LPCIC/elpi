(*e0a52a0856e6cc92109645b89bfa9e88 src/ast.mli *)
#1 "src/ast.mli"
open Util
module Func :
sig
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
  module Map : Map.S with type  key =  t
end
module Term :
sig
  type t =
    | Const of Func.t 
    | App of t * t list 
    | Lam of Func.t * t 
    | CData of CData.t 
    | Quoted of quote 
  and quote = {
    data: string ;
    loc: Loc.t ;
    kind: string option }[@@deriving show]
  val pp :
    Ppx_deriving_runtime_proxy.Format.formatter -> t -> Ppx_deriving_runtime_proxy.unit
  val show : t -> Ppx_deriving_runtime_proxy.string
  val pp_quote :
    Ppx_deriving_runtime_proxy.Format.formatter ->
      quote -> Ppx_deriving_runtime_proxy.unit
  val show_quote : quote -> Ppx_deriving_runtime_proxy.string
  exception NotInProlog of Loc.t * string 
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
module Clause :
sig
  type attribute =
    | Name of string 
    | After of string 
    | Before of string 
    | If of string [@@deriving show]
  val pp_attribute :
    Ppx_deriving_runtime_proxy.Format.formatter ->
      attribute -> Ppx_deriving_runtime_proxy.unit
  val show_attribute : attribute -> Ppx_deriving_runtime_proxy.string
  type ('term, 'attributes) t =
    {
    loc: Loc.t ;
    attributes: 'attributes ;
    body: 'term }[@@deriving show]
  val pp :
    (Ppx_deriving_runtime_proxy.Format.formatter ->
       'term -> Ppx_deriving_runtime_proxy.unit)
      ->
      (Ppx_deriving_runtime_proxy.Format.formatter ->
         'attributes -> Ppx_deriving_runtime_proxy.unit)
        ->
        Ppx_deriving_runtime_proxy.Format.formatter ->
          ('term, 'attributes) t -> Ppx_deriving_runtime_proxy.unit
  val show :
    (Ppx_deriving_runtime_proxy.Format.formatter ->
       'term -> Ppx_deriving_runtime_proxy.unit)
      ->
      (Ppx_deriving_runtime_proxy.Format.formatter ->
         'attributes -> Ppx_deriving_runtime_proxy.unit)
        -> ('term, 'attributes) t -> Ppx_deriving_runtime_proxy.string
end
module Chr :
sig
  type attribute =
    | Name of string 
    | If of string [@@deriving show]
  val pp_attribute :
    Ppx_deriving_runtime_proxy.Format.formatter ->
      attribute -> Ppx_deriving_runtime_proxy.unit
  val show_attribute : attribute -> Ppx_deriving_runtime_proxy.string
  type sequent = {
    eigen: Term.t ;
    context: Term.t ;
    conclusion: Term.t }
  and 'attribute t =
    {
    to_match: sequent list ;
    to_remove: sequent list ;
    guard: Term.t option ;
    new_goal: sequent option ;
    attributes: 'attribute ;
    loc: Loc.t }[@@deriving show]
  val pp_sequent :
    Ppx_deriving_runtime_proxy.Format.formatter ->
      sequent -> Ppx_deriving_runtime_proxy.unit
  val show_sequent : sequent -> Ppx_deriving_runtime_proxy.string
  val pp :
    (Ppx_deriving_runtime_proxy.Format.formatter ->
       'attribute -> Ppx_deriving_runtime_proxy.unit)
      ->
      Ppx_deriving_runtime_proxy.Format.formatter ->
        'attribute t -> Ppx_deriving_runtime_proxy.unit
  val show :
    (Ppx_deriving_runtime_proxy.Format.formatter ->
       'attribute -> Ppx_deriving_runtime_proxy.unit)
      -> 'attribute t -> Ppx_deriving_runtime_proxy.string
  val create :
    ?to_match:sequent list ->
      ?to_remove:sequent list ->
        ?guard:Term.t ->
          ?new_goal:sequent ->
            attributes:'attribute -> loc:Loc.t -> unit -> 'attribute t
end
module Macro :
sig
  type ('name, 'term) t = {
    loc: Loc.t ;
    name: 'name ;
    body: 'term }[@@deriving show]
  val pp :
    (Ppx_deriving_runtime_proxy.Format.formatter ->
       'name -> Ppx_deriving_runtime_proxy.unit)
      ->
      (Ppx_deriving_runtime_proxy.Format.formatter ->
         'term -> Ppx_deriving_runtime_proxy.unit)
        ->
        Ppx_deriving_runtime_proxy.Format.formatter ->
          ('name, 'term) t -> Ppx_deriving_runtime_proxy.unit
  val show :
    (Ppx_deriving_runtime_proxy.Format.formatter ->
       'name -> Ppx_deriving_runtime_proxy.unit)
      ->
      (Ppx_deriving_runtime_proxy.Format.formatter ->
         'term -> Ppx_deriving_runtime_proxy.unit)
        -> ('name, 'term) t -> Ppx_deriving_runtime_proxy.string
end
module Type :
sig
  type attribute =
    | External 
    | Index of int list [@@deriving show]
  val pp_attribute :
    Ppx_deriving_runtime_proxy.Format.formatter ->
      attribute -> Ppx_deriving_runtime_proxy.unit
  val show_attribute : attribute -> Ppx_deriving_runtime_proxy.string
  type 'attribute t =
    {
    loc: Loc.t ;
    attributes: 'attribute ;
    name: Func.t ;
    ty: Term.t }[@@deriving show]
  val pp :
    (Ppx_deriving_runtime_proxy.Format.formatter ->
       'attribute -> Ppx_deriving_runtime_proxy.unit)
      ->
      Ppx_deriving_runtime_proxy.Format.formatter ->
        'attribute t -> Ppx_deriving_runtime_proxy.unit
  val show :
    (Ppx_deriving_runtime_proxy.Format.formatter ->
       'attribute -> Ppx_deriving_runtime_proxy.unit)
      -> 'attribute t -> Ppx_deriving_runtime_proxy.string
end
module Mode :
sig
  type 'name t = {
    name: 'name ;
    args: bool list ;
    loc: Loc.t }[@@deriving show]
  val pp :
    (Ppx_deriving_runtime_proxy.Format.formatter ->
       'name -> Ppx_deriving_runtime_proxy.unit)
      ->
      Ppx_deriving_runtime_proxy.Format.formatter ->
        'name t -> Ppx_deriving_runtime_proxy.unit
  val show :
    (Ppx_deriving_runtime_proxy.Format.formatter ->
       'name -> Ppx_deriving_runtime_proxy.unit)
      -> 'name t -> Ppx_deriving_runtime_proxy.string
end
module TypeAbbreviation :
sig
  type 'name t = {
    name: 'name ;
    value: Term.t ;
    nparams: int ;
    loc: Loc.t }[@@deriving show]
  val pp :
    (Ppx_deriving_runtime_proxy.Format.formatter ->
       'name -> Ppx_deriving_runtime_proxy.unit)
      ->
      Ppx_deriving_runtime_proxy.Format.formatter ->
        'name t -> Ppx_deriving_runtime_proxy.unit
  val show :
    (Ppx_deriving_runtime_proxy.Format.formatter ->
       'name -> Ppx_deriving_runtime_proxy.unit)
      -> 'name t -> Ppx_deriving_runtime_proxy.string
end
module Program :
sig
  type decl =
    | Begin of Loc.t 
    | Namespace of Loc.t * Func.t 
    | Constraint of Loc.t * Func.t list 
    | Shorten of Loc.t * Func.t * Func.t 
    | End of Loc.t 
    | Accumulated of Loc.t * (Digest.t * decl list) 
    | Clause of (Term.t, Clause.attribute list) Clause.t 
    | Local of Func.t 
    | Mode of Func.t Mode.t list 
    | Chr of Chr.attribute list Chr.t 
    | Macro of (Func.t, Term.t) Macro.t 
    | Type of Type.attribute list Type.t 
    | TypeAbbreviation of Func.t TypeAbbreviation.t [@@deriving show]
  val pp_decl :
    Ppx_deriving_runtime_proxy.Format.formatter ->
      decl -> Ppx_deriving_runtime_proxy.unit
  val show_decl : decl -> Ppx_deriving_runtime_proxy.string
  val mkLocal : string -> decl
  type t = decl list[@@deriving show]
  val pp :
    Ppx_deriving_runtime_proxy.Format.formatter -> t -> Ppx_deriving_runtime_proxy.unit
  val show : t -> Ppx_deriving_runtime_proxy.string
end
module Goal :
sig
  type t = (Loc.t * Term.t)[@@deriving show]
  val pp :
    Ppx_deriving_runtime_proxy.Format.formatter -> t -> Ppx_deriving_runtime_proxy.unit
  val show : t -> Ppx_deriving_runtime_proxy.string
end
open CData
val cfloat : float cdata
val cint : int cdata
val cstring : string cdata
val cloc : Loc.t cdata
module Structured :
sig
  type program =
    {
    macros: (Func.t, Term.t) Macro.t list ;
    types: tattribute Type.t list ;
    type_abbrevs: Func.t TypeAbbreviation.t list ;
    modes: Func.t Mode.t list ;
    body: block list }
  and block =
    | Locals of Func.t list * program 
    | Clauses of (Term.t, attribute) Clause.t list 
    | Namespace of Func.t * program 
    | Shorten of Func.t shorthand list * program 
    | Constraints of Func.t list * cattribute Chr.t list * program 
  and attribute =
    {
    insertion: insertion option ;
    id: string option ;
    ifexpr: string option }
  and insertion =
    | Before of string 
    | After of string 
  and cattribute = {
    cid: string ;
    cifexpr: string option }
  and tattribute =
    | External 
    | Indexed of int list 
  and 'a shorthand = {
    iloc: Loc.t ;
    full_name: 'a ;
    short_name: 'a }[@@deriving show]
  val pp_program :
    Ppx_deriving_runtime_proxy.Format.formatter ->
      program -> Ppx_deriving_runtime_proxy.unit
  val show_program : program -> Ppx_deriving_runtime_proxy.string
  val pp_block :
    Ppx_deriving_runtime_proxy.Format.formatter ->
      block -> Ppx_deriving_runtime_proxy.unit
  val show_block : block -> Ppx_deriving_runtime_proxy.string
  val pp_attribute :
    Ppx_deriving_runtime_proxy.Format.formatter ->
      attribute -> Ppx_deriving_runtime_proxy.unit
  val show_attribute : attribute -> Ppx_deriving_runtime_proxy.string
  val pp_insertion :
    Ppx_deriving_runtime_proxy.Format.formatter ->
      insertion -> Ppx_deriving_runtime_proxy.unit
  val show_insertion : insertion -> Ppx_deriving_runtime_proxy.string
  val pp_cattribute :
    Ppx_deriving_runtime_proxy.Format.formatter ->
      cattribute -> Ppx_deriving_runtime_proxy.unit
  val show_cattribute : cattribute -> Ppx_deriving_runtime_proxy.string
  val pp_tattribute :
    Ppx_deriving_runtime_proxy.Format.formatter ->
      tattribute -> Ppx_deriving_runtime_proxy.unit
  val show_tattribute : tattribute -> Ppx_deriving_runtime_proxy.string
  val pp_shorthand :
    (Ppx_deriving_runtime_proxy.Format.formatter -> 'a -> Ppx_deriving_runtime_proxy.unit)
      ->
      Ppx_deriving_runtime_proxy.Format.formatter ->
        'a shorthand -> Ppx_deriving_runtime_proxy.unit
  val show_shorthand :
    (Ppx_deriving_runtime_proxy.Format.formatter -> 'a -> Ppx_deriving_runtime_proxy.unit)
      -> 'a shorthand -> Ppx_deriving_runtime_proxy.string
end

