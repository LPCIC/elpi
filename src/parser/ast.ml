(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Util

module Loc = Loc
module Func = struct

  module Self = struct

  type t = string
  let compare = String.compare

  (* Hash consing *)
  let from_string =
   let h = Hashtbl.create 37 in
   let rec aux = function
    | "nil" -> aux "[]"
    | "cons" -> aux "::"
    | "&" -> aux "," (* legacy parser *)
    | x ->
       try Hashtbl.find h x
       with Not_found -> Hashtbl.add h x x ; x
   in
     aux

  let pp fmt s = Format.fprintf fmt "%s" s
  let show x = x
  let equal x y = x == y || x = y (* Resilient to unmarshaling *)
  let truef = from_string "true"
  let andf = from_string ","
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
  let arrowf = from_string "->"
  let sequentf = from_string "?-"
  let ctypef = from_string "ctype"

  let propf = from_string "prop"

  let typef = from_string "type"
  let mainf = from_string "main"

  
  let dummyname = from_string "%dummy"
  let spillf = from_string "%spill"

  end

  let is_uvar_name s =
    let c = s.[0] in
    ('A' <= c && c <= 'Z')

  include Self
  module Map = Map.Make(Self)
  module Set = Set.Make(Self)

end

module Mode = struct

  type t = Util.arg_mode = Input | Output
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
[@@deriving show, ord]


module TypeExpression = struct

  type 'attribute t_ =
    | TConst of Func.t
    | TApp of Func.t * 'attribute t * 'attribute t list
    | TPred of 'attribute * (Mode.t * 'attribute t) list
    | TArr of 'attribute t * 'attribute t
  and 'a t = { tit : 'a t_; tloc : Loc.t }
  [@@ deriving show, ord]

end
  
module Term = struct
  
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

let mkC loc x = { loc; it = CData x }
let mkLam loc x ty t = { loc; it = Lam (Func.from_string x,ty,t) }
let mkNil loc = {loc; it = Const Func.nilf }
let mkParens loc t = { loc; it = Parens t }
let mkQuoted loc pad s =
  let strip n m loc = { loc with Loc.source_start = loc.Loc.source_start + n;
                                 Loc.source_stop = loc.Loc.source_stop - m;
             } in
  (* Printf.eprintf "mkQuoted '%s'\n" s; *)
  let rec find_data i pad =
    match s.[i] with
    (* | '{' -> assert false; find_data (i+1) (pad+1) *)
    | ':' ->
       let len = String.length s in
       let rec find_space i =
         if i >= len then
           raise (NotInProlog(loc,"syntax error: bad named quotation: {{"^s^"}}.\nDid you separate the name from the data with a space as in {{:name data}} ?."));
         match s.[i] with
         | ' ' -> i 
         | '\n' -> i 
         | _ -> find_space (i+1) in
       let space_after = find_space 0 in
  (* Printf.eprintf "mkQuoted space_after '%d'\n" space_after; *)
       let kind = String.sub s 1 (space_after-1) in
       let data = String.sub s (space_after+1) (String.length s - space_after-1) in
       let qloc = strip (space_after+1+pad) pad loc in
  (* Printf.eprintf "mkQuoted data '%s'\n" data;
  Printf.eprintf "mkQuoted kind '%s'\n" kind;
  Printf.eprintf "mkQuoted qloc '%s'\n" (Loc.show qloc); *)
       { qloc; data; kind = Some kind }
    | _ ->
      let qloc = strip pad pad loc in
  (* Printf.eprintf "mkQuoted qloc '%s'\n" (Loc.show qloc); *)
       { qloc; data = String.sub s i (String.length s - i - i); kind = None }
  in
    { loc; it = Quoted (find_data 0 pad) }
let mkSeq ?loc (l : t list) =
 let rec aux = function
    [] -> assert false
  | [e] -> e
  | { it = Parens it} :: tl -> aux (it :: tl)
  | hd::tl ->
      let tl = aux tl in
      { loc = Loc.merge hd.loc tl.loc; it = App({ it = Const Func.consf; loc = hd.loc },[hd;tl]) }
 in
   let l = aux l in
   match loc with None -> l | Some loc -> { l with loc }
let mkCast loc t ty = { loc; it = Cast(t,ty) }

let rec best_effort_pp = function
 | Lam (x,_,t) -> "x\\" ^ best_effort_pp t.it
 | CData c -> CData.show c
 | Quoted _ -> "{{ .. }}"
 | Cast _ -> "(.. : ..)"
 | _ -> ".."

let mkApp loc = function
(* FG: for convenience, we accept an empty list of arguments *)
  | [{ it = (App _ | Const _ | Quoted _) } as c] -> c
  | { it = App(c,l1) } ::l2 -> { loc; it = App(c,l1@l2) }
  | { it = (Const _ | Quoted _) } as c::l2 -> { loc; it = App(c,l2) }
  | [] -> anomaly ~loc "empty application"
  | x::_ -> raise (NotInProlog(loc,"syntax error: the head of an application must be a constant or a variable, got: " ^ best_effort_pp x.it))

let mkAppF loc (cloc, c) l =
  if l = [] then anomaly ~loc "empty application";
  if c = "," then
      { loc; it =
        App({ it = Const c; loc = cloc },
          List.concat_map (function 
            | { loc; it = Parens { it = App({it=Const ","}, l)}} -> l
            | { loc; it = App({it=Const ","}, l)} -> l
            | x -> [x]
        ) l) }
  else
    { loc; it = App({ it = Const c; loc = cloc },l) }



let last_warn_impl = ref (Loc.initial "(dummy)")
let warn_impl { it; loc } =
  match it with
  | App({ it = Const "=>" }, _ ) ->
      if !last_warn_impl <> loc then
        warn ~loc
{|The standard λProlog infix operator for implication => has higher precedence
than conjunction. This means that 'A => B, C' reads '(A => B), C'.
This is a common mistake since it makes A only available to B (and not to C
as many newcomers may expect).
If this is really what you want write '(A => B), C' to silence this warning.
Otherwise write 'A => (B, C)', or use the alternative implication operator ==>.
Infix ==>  has lower precedence than conjunction, hence
'A ==> B, C' reads 'A ==> (B, C)' and means the same as 'A => (B, C)'.|};
      last_warn_impl := loc
  | _ -> ()

let warn_impl_conj_precedence = function
  | App({ it = Const "," }, args ) ->
      begin match List.rev args with
      | { it = Const "!"} :: args_but_last -> ()
      | _ :: args_but_last -> List.iter warn_impl args_but_last
      | _ -> ()
      end
  | _ -> ()

let mkAppF loc (cloc,c) l =
  let t = mkAppF loc (cloc,c) l in
  warn_impl_conj_precedence t.it;
  t


let fresh_uv_names = ref (-1);;
let mkFreshUVar loc = incr fresh_uv_names; { loc; it = Const (Func.from_string ("_" ^ string_of_int !fresh_uv_names)) }
let fresh_names = ref (-1);;
let mkFreshName loc = incr fresh_names; { loc; it = Const (Func.from_string ("__" ^ string_of_int !fresh_names)) }
let mkCon loc c = { loc; it = Const (Func.from_string c) }
let mkConst loc c = { loc; it = Const c }

end

module Clause = struct
  
  type ('term,'attributes,'spill) t = {
    loc : Loc.t;
    attributes : 'attributes;
    body : 'term;
    needs_spilling : 'spill;
  }
  [@@deriving show, ord]

end

module Chr = struct

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

module Macro = struct

  type ('name,'term) t = {
     loc : Loc.t;
     name : 'name;
     body : 'term
  }
  [@@deriving show, ord]

end

module Type = struct

  type ('attribute,'inner_attribute) t = {
    loc : Loc.t;
    attributes : 'attribute;
    name : Func.t;
    ty : 'inner_attribute TypeExpression.t;
  }
  [@@deriving show, ord]

end

module TypeAbbreviation = struct

  type 'ty closedTypeexpression = 
    | Lam of Func.t * Loc.t * 'ty closedTypeexpression 
    | Ty of 'ty
  [@@ deriving show, ord]

  type ('name,'ty) t =
    { name : 'name; value : 'ty closedTypeexpression; nparams : int; loc : Loc.t }
  [@@ deriving show, ord]

end


module Program = struct

  type decl =
    (* Blocks *)
    | Begin of Loc.t
    | Namespace of Loc.t * Func.t
    | Constraint of Loc.t * Func.t list * Func.t list
    | Shorten of Loc.t * (Func.t * Func.t) list (* prefix suffix *)
    | End of Loc.t

    | Accumulated of Loc.t * parser_output list

    (* data *)
    | Clause of (Term.t, raw_attribute list,unit) Clause.t
    | Chr of (raw_attribute list,Term.t) Chr.t
    | Macro of (Func.t, Term.t) Macro.t
    | Kind of (raw_attribute list,raw_attribute list) Type.t list
    | Type of (raw_attribute list,raw_attribute list) Type.t list
    | Pred of (raw_attribute list,raw_attribute list) Type.t
    | TypeAbbreviation of (Func.t,raw_attribute list TypeExpression.t) TypeAbbreviation.t
    | Ignored of Loc.t
  and parser_output = { file_name : string; digest : Digest.t; ast : decl list }
  [@@deriving show]


type t = decl list [@@deriving show]

end

module Goal = struct

  type t = Term.t
  let pp fmt t = Term.pp fmt t
  let show x = Format.asprintf "%a" pp x

end
 
module Fmt = Format

let cfloat =
  CData.(declare {
    data_name = "float";
    data_pp = (fun f x -> Fmt.fprintf f "%f" x);
    data_compare = Float.compare;
    data_hash = Hashtbl.hash;
    data_hconsed = false;
  })
let cint =
  CData.(declare {
    data_name = "int";
    data_pp = (fun f x -> Fmt.fprintf f "%d" x);
    data_compare = Int.compare;
    data_hash = Hashtbl.hash;
    data_hconsed = false;
  })
let cstring =
  CData.(declare {
    data_name = "string";
    data_pp = (fun f x -> Fmt.fprintf f "%s" x);
    data_compare = String.compare;
    data_hash = Hashtbl.hash;
    data_hconsed = true;
  })
let cloc =
  CData.(declare {
    data_name = "loc";
    data_pp = Util.Loc.pp;
    data_compare = Stdlib.compare;
    data_hash = Hashtbl.hash;
    data_hconsed = false;
  })

module Structured = struct

type program = {
  macros : (Func.t, Term.t) Macro.t list;
  kinds : (unit,unit) Type.t list;
  types : (tattribute,functionality) Type.t list;
  type_abbrevs : (Func.t,functionality TypeExpression.t) TypeAbbreviation.t list;
  body : block list;
}
and cattribute = {
  cid : string;
  cifexpr : string option
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

