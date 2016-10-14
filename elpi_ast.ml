(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module Func = struct

  module Self = struct

  type t = string
  let compare = String.compare

  (* Hash consing *)
  let from_string =
   let h = Hashtbl.create 37 in
   function x ->
    try Hashtbl.find h x
    with Not_found -> Hashtbl.add h x x ; x

  let pp fmt s = Format.fprintf fmt "%s" s
  let show x = x
  let equal = (==)
  let truef = from_string "true"
  let andf = from_string ","
  let andf2 = from_string "&"
  let orf = from_string ";"
  let implf = from_string "=>"
  let rimplf = from_string ":-"
  let cutf = from_string "!"
  let pif = from_string "pi"
  let sigmaf = from_string "sigma"
  let eqf = from_string "="
  let isf = from_string "is"
  let consf = from_string "::"
  let nilf = from_string "[]"
  let letf = from_string ":="
  let arrowf = from_string "->"
  let sequentf = from_string "?-"
  
  let dummyname = from_string "%dummy"
  let spillf = from_string "%spill"

  end

  include Self
  module Map = Map.Make(Self)

end

type term =
   Const of Func.t
 | Custom of Func.t
 | App of term * term list
 | Lam of Func.t * term
 | String of Func.t
 | Int of int
 | Float of float
[@@deriving show, eq, ord]

let mkLam x t = Lam (Func.from_string x,t)
let mkNil = Const Func.nilf
let mkString str = String (Func.from_string str)
let mkInt i = Int i
let mkFloat f = Float f
let mkSeq l =
 let rec aux =
  function
    [] -> assert false
  | [e] -> e
  | hd::tl -> App(Const Func.consf,[hd;aux tl])
 in
  aux l
let mkIs x f = App(Const Func.isf,[x;f])

type clause = {
  loc : Ploc.t [@printer fun _ _ -> ()];
  id : string option;
  insert : ([ `Before | `After ] * string) option;
  body : term;
}[@@deriving show]

type ('term,'func_t) chr = {
  to_match : ('term * 'term) list;
  to_remove : ('term * 'term) list;
  alignement : 'func_t list;
  guard : 'term option;
  new_goal : 'term option;
  depth : int [@default 0];
  nargs : int [@default 0];
}
[@@deriving show, create]

type decl =
   Clause of clause
 | Local of Func.t
 | Begin
 | End
 | Mode of (Func.t * bool list * (Func.t * (Func.t * Func.t) list) option) list
 | Constraint of Func.t list
 | Chr of (term, Func.t) chr
 | Accumulated of decl list
 | Macro of Func.t * term
 | Type of Func.t * term
[@@deriving show]

let mkLocal x = Local (Func.from_string x)

type program = decl list [@@deriving show]
type goal = term

exception NotInProlog

let mkApp = function
(* FG: for convenience, we accept an empty list of arguments *)
  | [(App _ | Custom _ | Const _) as c] -> c
  | App(c,l1)::l2 -> App(c,l1@l2)
  | (Custom _ | Const _) as c::l2 -> App(c,l2)
  | _ -> raise NotInProlog

let fresh_uv_names = ref (-1);;
let mkFreshUVar () = incr fresh_uv_names; Const (Func.from_string ("_" ^ string_of_int !fresh_uv_names))
let fresh_names = ref (-1);;
let mkFreshName () = incr fresh_names; Const (Func.from_string ("__" ^ string_of_int !fresh_names))
let mkCon c = Const (Func.from_string c)
let mkCustom c = Custom (Func.from_string c)
