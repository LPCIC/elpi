(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module Func = struct

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
  let nilf = from_string "nil"
  let letf = from_string ":="
  let arrowf = from_string "->"

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

type clause = term
type decl =
   Clause of clause
 | Local of Func.t
 | Begin
 | End
 | Mode of (Func.t * bool list * (Func.t * (Func.t * Func.t) list) option) list
 | Constraint of Func.t list
 | Accumulated of decl list

let mkLocal x = Local (Func.from_string x)

type program = decl list
type goal = term

exception NotInProlog

let mkApp =
 function
    App(c,l1)::l2 -> App(c,l1@l2)
  | (Custom _ | Const _) as c::l2 -> App(c,l2)
  | _ -> raise NotInProlog

let fresh_uv_names = ref (-1);;
let mkFreshUVar () = incr fresh_uv_names; Const (Func.from_string ("_" ^ string_of_int !fresh_uv_names))
let fresh_names = ref (-1);;
let mkFreshName () = incr fresh_names; Const (Func.from_string ("__" ^ string_of_int !fresh_names))
let mkCon c = Const (Func.from_string c)
let mkCustom c = Custom (Func.from_string c)
