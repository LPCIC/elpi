(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open API
open RawData
open Utils
open BuiltInPredicate
open Notation

module Str = Re.Str

let register_eval, register_eval_ty, lookup_eval, eval_declaration =
 let rec str_of_ty n s =
   if n = 0 then s else s ^ " -> " ^ str_of_ty (n-1) s in
 let (evals : ('a, view list -> term) Hashtbl.t)
   =
     Hashtbl.create 17 in
 let declaration = ref [] in
 (fun nargs (s,tys) f ->
   tys |> List.iter (fun ty ->
     let ty =
       if nargs = 2 then
         Printf.sprintf "type (%s) %s." s (str_of_ty nargs ty)
       else
         Printf.sprintf "type %s %s." s (str_of_ty nargs ty) in
     declaration := BuiltIn.LPCode ty :: !declaration);
   Hashtbl.add evals (Constants.declare_global_symbol s) f),
 (fun s ty f ->
   declaration := BuiltIn.LPCode (Printf.sprintf "type %s %s." s ty) :: !declaration;
   Hashtbl.add evals (Constants.declare_global_symbol s) f),
 Hashtbl.find evals,
 (fun () -> List.rev !declaration)
;;

(* Traverses the expression evaluating all custom evaluable functions *)
let rec eval depth t =
  match look ~depth t with
  | Lam _ -> type_error "Evaluation of a lambda abstraction"
  | Builtin _ -> type_error "Evaluation of built-in predicate"
  | App (hd,arg,args) ->
     let f =
      try lookup_eval hd
      with Not_found ->
        function
        | [] -> assert false
        | x::xs -> mkApp hd (kool x) (List.map kool xs)  in
     let args = List.map (fun x -> look ~depth (eval depth x)) (arg::args) in
     f args
  | UnifVar _ -> error "Evaluation of a non closed term (maybe delay)"
  | Const hd as x ->
     let f =
      try lookup_eval hd
      with Not_found -> fun _ -> kool x in
     f []
  | (Nil | Cons _ as x) ->
      type_error ("Lists cannot be evaluated: " ^ RawPp.Debug.show_term (kool x))
  | CData _ as x -> kool x
;;

let register_evals n l f = List.iter (fun i -> register_eval n i f) l;;

let _ =
  let open RawOpaqueData in
  register_evals 2 [ "-",["A"] ; "i-",["int"] ; "r-",["float"] ] (function
   | [ CData x; CData y ] when ty2 int x y -> mkCData(morph2 int (-) x y)
   | [ CData x; CData y ] when ty2 float x y -> mkCData(morph2 float (-.) x y)
   | _ -> type_error "Wrong arguments to -/i-/r-") ;
  register_evals 2 [ "+",["int";"float"] ; "i+",["int"] ; "r+",["float"] ] (function
   | [ CData x; CData y ] when ty2 int x y -> mkCData(morph2 int (+) x y)
   | [ CData x; CData y ] when ty2 float x y -> mkCData(morph2 float (+.) x y)
   | _ -> type_error "Wrong arguments to +/i+/r+") ;
  register_eval 2 ("*",["int";"float"]) (function
   | [ CData x; CData y ] when ty2 int x y -> mkCData(morph2 int ( * ) x y)
   | [ CData x; CData y] when ty2 float x y -> mkCData(morph2 float ( *.) x y)
   | _ -> type_error "Wrong arguments to *") ;
  register_eval 2 ("/",["float"]) (function
   | [ CData x; CData y] when ty2 float x y -> mkCData(morph2 float ( /.) x y)
   | _ -> type_error "Wrong arguments to /") ;
  register_eval 2 ("mod",["int"]) (function
   | [ CData x; CData y ] when ty2 int x y -> mkCData(morph2 int (mod) x y)
   | _ -> type_error "Wrong arguments to mod") ;
  register_eval 2 ("div",["int"]) (function
   | [ CData x; CData y ] when ty2 int x y -> mkCData(morph2 int (/) x y)
   | _ -> type_error "Wrong arguments to div") ;
  register_eval 2 ("^",["string"]) (function
   | [ CData x; CData y ] when ty2 string x y ->
         of_string (to_string x ^ to_string y)
   | _ -> type_error "Wrong arguments to ^") ;
  register_evals 1 [ "~",["int";"float"] ; "i~",["int"] ; "r~",["float"] ] (function
   | [ CData x ] when is_int x -> mkCData(morph1 int (~-) x)
   | [ CData x ] when is_float x -> mkCData(morph1 float (~-.) x)
   | _ -> type_error "Wrong arguments to ~/i~/r~") ;
  register_evals 1 [ "abs",["int";"float"] ; "iabs",["int"] ; "rabs",["float"] ] (function
   | [ CData x ] when is_int x -> mkCData(map int int abs x)
   | [ CData x ] when is_float x -> mkCData(map float float abs_float x)
   | _ -> type_error "Wrong arguments to abs/iabs/rabs") ;
  register_eval 1 ("sqrt",["float"]) (function
   | [ CData x ] when is_float x -> mkCData(map float float sqrt x)
   | _ -> type_error "Wrong arguments to sqrt") ;
  register_eval 1 ("sin",["float"]) (function
   | [ CData x ] when is_float x -> mkCData(map float float sqrt x)
   | _ -> type_error "Wrong arguments to sin") ;
  register_eval 1 ("cos",["float"]) (function
   | [ CData x ] when is_float x -> mkCData(map float float cos x)
   | _ -> type_error "Wrong arguments to cosin") ;
  register_eval 1 ("arctan",["float"]) (function
   | [ CData x ] when is_float x -> mkCData(map float float atan x)
   | _ -> type_error "Wrong arguments to arctan") ;
  register_eval 1 ("ln",["float"]) (function
   | [ CData x ] when is_float x -> mkCData(map float float log x)
   | _ -> type_error "Wrong arguments to ln") ;
  register_eval_ty "int_to_real" "int -> float" (function
   | [ CData x ] when is_int x -> mkCData(map int float float_of_int x)
   | _ -> type_error "Wrong arguments to int_to_real") ;
  register_eval_ty "floor" "float -> int" (function
   | [ CData x ] when is_float x ->
         mkCData(map float int (fun x -> int_of_float (floor x)) x)
   | _ -> type_error "Wrong arguments to floor") ;
  register_eval_ty "ceil" "float -> int" (function
   | [ CData x ] when is_float x ->
         mkCData(map float int (fun x -> int_of_float (ceil x)) x)
   | _ -> type_error "Wrong arguments to ceil") ;
  register_eval_ty "truncate" "float -> int" (function
   | [ CData x ] when is_float x -> mkCData(map float int truncate x)
   | _ -> type_error "Wrong arguments to truncate") ;
  register_eval_ty "size" "string -> int" (function
   | [ CData x ] when is_string x ->
         of_int (String.length (to_string x))
   | _ -> type_error "Wrong arguments to size") ;
  register_eval_ty "chr" "int -> string" (function
   | [ CData x ] when is_int x ->
         of_string (String.make 1 (char_of_int (to_int x)))
   | _ -> type_error "Wrong arguments to chr") ;
  register_eval_ty "rhc" "string -> int" (function
   | [ CData x ] when is_string x && String.length (to_string x) = 1 ->
       of_int (int_of_char (to_string x).[0])
   | _ -> type_error "Wrong arguments to rhc") ;
  register_eval_ty "string_to_int" "string -> int" (function
   | [ CData x ] when is_string x -> of_int (int_of_string (to_string x))
   | _ -> type_error "Wrong arguments to string_to_int") ;
  register_eval_ty "int_to_string" "int -> string" (function
   | [ CData x ] when is_int x ->
         of_string (string_of_int (to_int x))
   | _ -> type_error "Wrong arguments to int_to_string") ;
  register_eval_ty "substring" "string -> int -> int -> string" (function
   | [ CData x ; CData i ; CData j ] when is_string x && ty2 int i j ->
       let x = to_string x and i = to_int i and j = to_int j in
       if i >= 0 && j >= 0 && String.length x >= i+j then
         of_string (String.sub x i j)
       else type_error "Wrong arguments to substring"
   | _ -> type_error "Wrong argument type to substring") ;
  register_eval_ty "real_to_string" "float -> string" (function
   | [ CData x ] when is_float x ->
         of_string (string_of_float (to_float x))
   | _ -> type_error "Wrong arguments to real_to_string")
;;

let really_input ic s ofs len =
  let rec unsafe_really_input read ic s ofs len =
    if len <= 0 then read else begin
      let r = input ic s ofs len in
      if r = 0
      then read
      else unsafe_really_input (read+r) ic s (ofs + r) (len - r)
    end
  in
  if ofs < 0 || len < 0 || ofs > Bytes.length s - len
  then invalid_arg "really_input"
  else unsafe_really_input 0 ic s ofs len

(* constant x occurs in term t with level d? *)
let occurs x d t =
   let rec aux t = match look ~depth:d t with
     | Const c                          -> c = x
     | Lam t                            -> aux t
     | App (c, v, vs)                   -> c = x || aux v || auxs vs
     | UnifVar (_, l)                   -> auxs l
     | Builtin (_, vs)                  -> auxs vs
     | Cons (v1, v2)                    -> aux v1 || aux v2
     | Nil
     | CData _                          -> false
   and auxs = function
     | []      -> false
     | t :: ts -> aux t || auxs ts
   in
   x < d && aux t

type polyop = {
  p : 'a. 'a -> 'a -> bool;
  psym : string;
  pname : string;
}

let typec = RawData.Constants.declare_global_symbol "pair"
let constructorc = RawData.Constants.declare_global_symbol "pr"
let tyast a b = Conversion.TyApp("pair",a,[b])
let readback_pair readback_a1 readback_a2 ~depth hyps csts st x =
  match RawData.look ~depth x with
  | RawData.App(c,x1,[x2]) when c == constructorc ->
      let st, x1, gls1 = readback_a1 ~depth hyps csts st x1 in
      let st, x2, gls2 = readback_a2 ~depth hyps csts st x2 in
      st, (x1,x2), gls1 @ gls2
  | _ -> raise (Conversion.TypeErr(tyast (Conversion.TyName "A") (Conversion.TyName "B"),depth,x))
let embed_pair embed_a1 embed_a2 ~depth hyps csts st x =
  let (x1,x2) = x in
  let st, x1, gls1 = embed_a1 ~depth hyps csts st x1 in
  let st, x2, gls2 = embed_a2 ~depth hyps csts st x2 in
  st, RawData.mkApp constructorc x1 [x2], gls1 @ gls2
let pair a1 a2 = let open Conversion in
  let ty = tyast a1.ty a2.ty in {
  ty;
  pp_doc = (PPX.Doc.adt ~doc:"Pair: the constructor is pr, since ',' is for conjunction" ~ty ~args:["pr","",[a1.ty;a2.ty]]);
  pp = (fun fmt (x1,x2) -> Format.fprintf fmt "(%a,%a)" a1.pp x1 a2.pp x2);
  embed = embed_pair a1.embed a2.embed;
  readback = readback_pair a1.readback a2.readback;
}

let typec = RawData.Constants.declare_global_symbol "triple"
let constructorc = RawData.Constants.declare_global_symbol "triple"
let tyast a b c = Conversion.TyApp("triple",a,[b;c])
let readback_triple readback_a1 readback_a2 readback_a3 ~depth hyps csts st x =
  match RawData.look ~depth x with
  | RawData.App(c,x1,[x2;x3]) when c == constructorc ->
      let st, x1, gls1 = readback_a1 ~depth hyps csts st x1 in
      let st, x2, gls2 = readback_a2 ~depth hyps csts st x2 in
      let st, x3, gls3 = readback_a3 ~depth hyps csts st x3 in
      st, (x1,x2,x3), gls1 @ gls2 @ gls3
  | _ -> raise (Conversion.TypeErr(tyast (Conversion.TyName "A") (Conversion.TyName "B") (Conversion.TyName "C"),depth,x))
let embed_triple embed_a1 embed_a2 embed_a3 ~depth hyps csts st x =
  let (x1,x2,x3) = x in
  let st, x1, gls1 = embed_a1 ~depth hyps csts st x1 in
  let st, x2, gls2 = embed_a2 ~depth hyps csts st x2 in
  let st, x3, gls3 = embed_a3 ~depth hyps csts st x3 in
  st, RawData.mkApp constructorc x1 [x2;x3], gls1 @ gls2 @ gls3
let triple a1 a2 a3 = let open Conversion in
  let ty = tyast a1.ty a2.ty a3.ty in {
  ty;
  pp_doc = (PPX.Doc.adt ~doc:"" ~ty ~args:["triple","",[a1.ty;a2.ty;a3.ty]]);
  pp = (fun fmt (x1,x2,x3) -> Format.fprintf fmt "(%a,%a,%a)" a1.pp x1 a2.pp x2 a3.pp x3);
  embed = embed_triple a1.embed a2.embed a3.embed;
  readback = readback_triple a1.readback a2.readback a3.readback;
}

let typec = RawData.Constants.declare_global_symbol "quadruple"
let constructorc = RawData.Constants.declare_global_symbol "quadruple"
let tyast a b c d = Conversion.TyApp("quadruple",a,[b;c;d])
let readback_quadruple readback_a1 readback_a2 readback_a3 readback_a4 ~depth hyps csts st x =
  match RawData.look ~depth x with
  | RawData.App(c,x1,[x2;x3;x4]) when c == constructorc ->
      let st, x1, gls1 = readback_a1 ~depth hyps csts st x1 in
      let st, x2, gls2 = readback_a2 ~depth hyps csts st x2 in
      let st, x3, gls3 = readback_a3 ~depth hyps csts st x3 in
      let st, x4, gls4 = readback_a4 ~depth hyps csts st x4 in
      st, (x1,x2,x3,x4), gls1 @ gls2 @ gls3 @ gls4
  | _ -> raise (Conversion.TypeErr(tyast (Conversion.TyName "A") (Conversion.TyName "B") (Conversion.TyName "C") (Conversion.TyName "D"),depth,x))
let embed_quadruple embed_a1 embed_a2 embed_a3 embed_a4 ~depth hyps csts st x =
  let (x1,x2,x3,x4) = x in
  let st, x1, gls1 = embed_a1 ~depth hyps csts st x1 in
  let st, x2, gls2 = embed_a2 ~depth hyps csts st x2 in
  let st, x3, gls3 = embed_a3 ~depth hyps csts st x3 in
  let st, x4, gls4 = embed_a4 ~depth hyps csts st x4 in
  st, RawData.mkApp constructorc x1 [x2;x3;x4], gls1 @ gls2 @ gls3 @ gls4
let quadruple a1 a2 a3 a4 = let open Conversion in
  let ty = tyast a1.ty a2.ty a3.ty a4.ty in {
  ty;
  pp_doc = (PPX.Doc.adt ~doc:"" ~ty ~args:["quadruple","",[a1.ty;a2.ty;a3.ty;a4.ty]]);
  pp = (fun fmt (x1,x2,x3,x4) -> Format.fprintf fmt "(%a,%a,%a,%a)" a1.pp x1 a2.pp x2 a3.pp x3 a4.pp x4);
  embed = embed_quadruple a1.embed a2.embed a3.embed a4.embed;
  readback = readback_quadruple a1.readback a2.readback a3.readback a4.readback;
}

let typec = RawData.Constants.declare_global_symbol "quintuple"
let constructorc = RawData.Constants.declare_global_symbol "quintuple"
let tyast a b c d e = Conversion.TyApp("quintuple",a,[b;c;d;e])
let readback_quintuple readback_a1 readback_a2 readback_a3 readback_a4 readback_a5 ~depth hyps csts st x =
  match RawData.look ~depth x with
  | RawData.App(c,x1,[x2;x3;x4;x5]) when c == constructorc ->
      let st, x1, gls1 = readback_a1 ~depth hyps csts st x1 in
      let st, x2, gls2 = readback_a2 ~depth hyps csts st x2 in
      let st, x3, gls3 = readback_a3 ~depth hyps csts st x3 in
      let st, x4, gls4 = readback_a4 ~depth hyps csts st x4 in
      let st, x5, gls5 = readback_a5 ~depth hyps csts st x5 in
      st, (x1,x2,x3,x4,x5), gls1 @ gls2 @ gls3 @ gls4 @ gls5
  | _ -> raise (Conversion.TypeErr(tyast (Conversion.TyName "A") (Conversion.TyName "B") (Conversion.TyName "C") (Conversion.TyName "D") (Conversion.TyName "E"),depth,x))
let embed_quintuple embed_a1 embed_a2 embed_a3 embed_a4 embed_a5 ~depth hyps csts st x =
  let (x1,x2,x3,x4,x5) = x in
  let st, x1, gls1 = embed_a1 ~depth hyps csts st x1 in
  let st, x2, gls2 = embed_a2 ~depth hyps csts st x2 in
  let st, x3, gls3 = embed_a3 ~depth hyps csts st x3 in
  let st, x4, gls4 = embed_a4 ~depth hyps csts st x4 in
  let st, x5, gls5 = embed_a5 ~depth hyps csts st x5 in
  st, RawData.mkApp constructorc x1 [x2;x3;x4;x5], gls1 @ gls2 @ gls3 @ gls4 @ gls5
let quintuple a1 a2 a3 a4 a5 = let open Conversion in
  let ty = tyast a1.ty a2.ty a3.ty a4.ty a5.ty in {
  ty;
  pp_doc = (PPX.Doc.adt ~doc:"" ~ty ~args:["quintuple","",[a1.ty;a2.ty;a3.ty;a4.ty;a5.ty]]);
  pp = (fun fmt (x1,x2,x3,x4,x5) -> Format.fprintf fmt "(%a,%a,%a,%a,%a)" a1.pp x1 a2.pp x2 a3.pp x3 a4.pp x4 a5.pp x5);
  embed = embed_quintuple a1.embed a2.embed a3.embed a4.embed a5.embed;
  readback = readback_quintuple a1.readback a2.readback a3.readback a4.readback a5.readback;
}

let typec = RawData.Constants.declare_global_symbol "option"
let constructor1c = RawData.Constants.declare_global_symbol "none"
let constructor2c = RawData.Constants.declare_global_symbol "some"
let tyast a = Conversion.TyApp("option",a,[])
let readback_option readback_a1 ~depth hyps csts st x =
  match RawData.look ~depth x with
  | RawData.App(c,x1,[]) when c == constructor2c ->
      let st, x1, gls1 = readback_a1 ~depth hyps csts st x1 in
      st, Some x1, gls1
  | RawData.Const c when c == constructor1c ->
      st, None, []
  | _ -> raise (Conversion.TypeErr(tyast (Conversion.TyName "A"),depth,x))
let embed_option embed_a1 ~depth hyps csts st x =
  match x with
  | None -> st, RawData.mkConst constructor1c, []
  | Some x1 ->
     let st, x1, gls1 = embed_a1 ~depth hyps csts st x1 in
     st, RawData.mkApp constructor2c x1 [], gls1
let option a1 = let open Conversion in
  let ty = tyast a1.ty in {
  ty;
  pp_doc = (PPX.Doc.adt ~doc:"The option type (aka Maybe)" ~ty ~args:["none","",[];"some","",[a1.ty]]);
  pp = (fun fmt -> function None -> Format.fprintf fmt "None" | Some x1 -> Format.fprintf fmt "(Some %a)" a1.pp x1);
  embed = embed_option a1.embed;
  readback = readback_option a1.readback;
}

let cmp = let open AlgebraicData in declare {
  ty = TyName "cmp";
  doc = "Result of a comparison";
  pp = (fun fmt i -> Format.fprintf fmt "%d" i);
  constructors = [
    K("eq", "", N, B 0,   M(fun ~ok ~ko i -> if i == 0 then ok else ko ()));
    K("lt", "", N, B ~-1, M(fun ~ok ~ko i -> if i < 0  then ok else ko ()));
    K("gt", "", N, B 1,   M(fun ~ok ~ko i -> if i > 0  then ok else ko ()))
  ]
}


let error_cmp_flex ~depth t1 t2 = error "cmp_term on non-ground terms"

let rec cmp_term ~depth t1 t2 =
  match look ~depth t1, look ~depth t2 with
  | Nil, Nil -> 0
  | Nil, (Cons _ | Const _ | App _ | Lam _ | Builtin _ | CData _ | UnifVar _) -> -1

  | Cons(x,xs), Cons(y,ys) ->
      let cmp_x = cmp_term ~depth x y in
      if cmp_x == 0 then cmp_term ~depth xs ys
      else cmp_x
  | Cons _, (Const _ | App _ | Lam _ | Builtin _ | CData _ | UnifVar _) -> -1
  | Cons _, Nil -> 1

  | Const c1, Const c2 -> c1 - c2
  | Const _, (App _ | Lam _ | Builtin _ | CData _ | UnifVar _) -> -1
  | Const _, (Cons _ | Nil) -> 1

  | Lam t1, Lam t2 -> cmp_term ~depth:(depth+1) t1 t2
  | Lam _, (App _ | Builtin _ | CData _ | UnifVar _) -> -1
  | Lam _, (Const _ | Cons _ | Nil) -> 1

  | App(c1,x,xs), App(c2,y,ys) ->
      let cmp_c1 = c1 - c2 in
      if cmp_c1 == 0 then
        let cmp_x = cmp_term ~depth x y in
        if cmp_x == 0 then cmp_terms ~depth xs ys else cmp_x
      else cmp_c1
  | App _, (Builtin _ | CData _ | UnifVar _) -> -1
  | App _, (Lam _ | Const _ | Cons _ | Nil) -> 1

  | Builtin(c1,xs), Builtin(c2,ys) ->
      let cmp_c1 = cmp_builtin c1 c2 in
      if cmp_c1 == 0 then cmp_terms ~depth xs ys else cmp_c1
  | Builtin _, (CData _ | UnifVar _) -> -1
  | Builtin _, (App _ | Lam _ | Const _ | Cons _ | Nil) -> 1

  | CData d1, CData d2 -> RawOpaqueData.compare d1 d2
  | CData _, UnifVar _ -> -1
  | CData _, (Builtin _ | App _ | Lam _ | Const _ | Cons _ | Nil) -> 1

  | UnifVar(b1,xs), UnifVar(b2,ys) ->
      if FlexibleData.Elpi.equal b1 b2 then
        if cmp_terms ~depth xs ys == 0 then 0
        else error_cmp_flex ~depth t1 t2
      else error_cmp_flex ~depth t1 t2
  | UnifVar _, (CData _ | Builtin _ | App _ | Lam _ | Const _ | Cons _ | Nil) -> 1

and cmp_terms ~depth l1 l2 =
  match l1, l2 with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | x :: xs, y :: ys ->
      let cmp_x = cmp_term ~depth x y in
      if cmp_x == 0 then cmp_terms ~depth xs ys else cmp_x

let rec check_ground ~depth t =
  match look ~depth t with
  | Nil | Const _ | CData _ -> ()
  | Lam t -> check_ground ~depth:(depth + 1) t
  | Cons(x,xs) -> check_ground ~depth x; check_ground ~depth xs
  | Builtin(_,l) -> List.iter (check_ground ~depth) l
  | App(_,x,xs) -> check_ground ~depth x; List.iter (check_ground ~depth) xs
  | UnifVar _ -> raise No_clause

(** Core built-in ********************************************************* *)

let core_builtins = let open BuiltIn in let open Conversion in [

  LPDoc " == Core builtins =====================================";

  LPDoc " -- Logic --";

  LPCode "pred true.";
  LPCode "true.";

  LPCode "pred fail.";
  LPCode "pred false.";

  LPCode "pred (=) o:A, o:A.";
  LPCode "X = X.";

  MLData BuiltInData.int;
  MLData BuiltInData.string;
  MLData BuiltInData.float;

  LPCode "pred (;) o:prop, o:prop.";
  LPCode "(A ; _) :- A.";
  LPCode "(_ ; B) :- B.";

  LPCode "type (:-) prop -> prop -> prop.";
  LPCode "type (:-) prop -> list prop -> prop.";
  LPCode "type (,) variadic prop prop.";
  LPCode "type uvar A.";
  LPCode "type (as) A -> A -> A.";
  LPCode "type (=>) prop -> prop -> prop.";
  LPCode "type (=>) list prop -> prop -> prop.";

  LPDoc " -- Control --";

  (* This is not implemented here, since the API had no access to the
   * choice points *)
  LPCode "external pred !. % The cut operator";

  LPCode "pred not i:prop.";
  LPCode "not X :- X, !, fail.";
  LPCode "not _.";

  (* These are not implemented here since the API has no access to the
   * store of syntactic constraints *)
  LPCode ("% [declare_constraint C Keys] declares C with Keys (a list of variables).\n"^
          "external pred declare_constraint i:any, i:list any.");
  LPCode "external pred print_constraints. % prints all constraints";

  MLCode(Pred("halt", VariadicIn(BuiltInData.any, "halts the program and print the terms"),in_raw_ctx,
  (fun args ~depth _ _ ->
     if args = [] then error "halt"
     else
       let b = Buffer.create 80 in
       let fmt = Format.formatter_of_buffer b in
       Format.fprintf fmt "%a%!" (RawPp.list (RawPp.term depth) " ") args;
       error (Buffer.contents b))),
  DocAbove);

  LPCode "pred stop.";
  LPCode "stop :- halt.";

  LPDoc " -- Evaluation --";

  MLCode(Pred("calc",
    In(BuiltInData.poly "A",  "Expr",
    Out(BuiltInData.poly "A", "Out",
    Easy          "unifies Out with the value of Expr. It can be used in tandem with spilling, eg [f {calc (N + 1)}]")),in_raw_ctx,
  (fun t _ ~depth -> !:(eval depth t))),
  DocAbove);

  LPCode "pred (is) o:A, i:A.";
  LPCode "X is Y :- calc Y X.";

  ] @ eval_declaration () @ [

  LPDoc " -- Arithmetic tests --";

  ] @ List.map (fun { p; psym; pname } ->

  MLCode(Pred(pname,
    In(BuiltInData.poly "A","X",
    In(BuiltInData.poly "A","Y",
    Easy     ("checks if X " ^ psym ^ " Y. Works for string, int and float"))),in_raw_ctx,
  (fun t1 t2 ~depth ->
     let open RawOpaqueData in
     let t1 = look ~depth (eval depth t1) in
     let t2 = look ~depth (eval depth t2) in
     match t1, t2 with
     | CData x, CData y ->
          if ty2 int x y then let out = to_int in
            if p (out x) (out y) then () else raise No_clause
          else if ty2 float x y then let out = to_float in
            if p (out x) (out y) then () else raise No_clause
          else if ty2 string x y then let out = to_string in
            if p (out x) (out y) then () else raise No_clause
          else 
        type_error ("Wrong arguments to " ^ psym ^ " (or to " ^ pname^ ")")
     (* HACK: grundlagen.elpi uses the "age" of constants *)
     | Const t1, Const t2 ->
        let is_lt = if t1 < 0 && t2 < 0 then p t2 t1 else p t1 t2 in
        if not is_lt then raise No_clause else ()
     | _ -> type_error ("Wrong arguments to " ^psym^ " (or to " ^pname^ ")"))),
  DocAbove))

    [ { p = (<);  psym = "<";  pname = "lt_" } ;
      { p = (>);  psym = ">";  pname = "gt_" } ;
      { p = (<=); psym = "=<"; pname = "le_" } ;
      { p = (>=); psym = ">="; pname = "ge_" } ]

  @ [

  LPCode "type (<), (>), (=<), (>=) A -> A -> prop.";
  LPCode "X  > Y  :- gt_ X Y.";
  LPCode "X  < Y  :- lt_ X Y.";
  LPCode "X  =< Y :- le_ X Y.";
  LPCode "X  >= Y :- ge_ X Y.";

  LPCode "type (i<), (i>), (i=<), (i>=) int -> int -> prop.";
  LPCode "X i< Y  :- lt_ X Y.";
  LPCode "X i> Y  :- gt_ X Y.";
  LPCode "X i=< Y :- le_ X Y.";
  LPCode "X i>= Y :- ge_ X Y.";

  LPCode "type (r<), (r>), (r=<), (r>=) float -> float -> prop.";
  LPCode "X r< Y  :- lt_ X Y.";
  LPCode "X r> Y  :- gt_ X Y.";
  LPCode "X r=< Y :- le_ X Y.";
  LPCode "X r>= Y :- ge_ X Y.";

  LPCode "type (s<), (s>), (s=<), (s>=) string -> string -> prop.";
  LPCode "X s< Y  :- lt_ X Y.";
  LPCode "X s> Y  :- gt_ X Y.";
  LPCode "X s=< Y :- le_ X Y.";
  LPCode "X s>= Y :- ge_ X Y.";

  LPDoc " -- Standard data types (supported in the FFI) --";

  LPCode "kind list type -> type.";
  LPCode "type (::) X -> list X -> list X.";
  LPCode "type ([]) list X.";

  MLData BuiltInData.bool;
  MLData BuiltInData.char;

  MLData (pair (BuiltInData.poly "A") (BuiltInData.poly "B"));

  LPCode "pred fst  i:pair A B, o:A.";
  LPCode "fst (pr A _) A.";
  LPCode "pred snd  i:pair A B, o:B.";
  LPCode "snd (pr _ B) B.";

  MLData (triple (BuiltInData.poly "A") (BuiltInData.poly "B") (BuiltInData.poly "C"));

  LPCode "pred triple_1  i:triple A1 A2 A3, o:A1.";
  LPCode "triple_1 (triple X _ _) X.";
  LPCode "pred triple_2  i:triple A1 A2 A3, o:A2.";
  LPCode "triple_2 (triple _ X _) X.";
  LPCode "pred triple_3  i:triple A1 A2 A3, o:A3.";
  LPCode "triple_3 (triple _ _ X) X.";

  MLData (quadruple (BuiltInData.poly "A") (BuiltInData.poly "B") (BuiltInData.poly "C") (BuiltInData.poly "D"));

  LPCode "pred quadruple_1  i:quadruple A1 A2 A3 A4, o:A1.";
  LPCode "quadruple_1 (quadruple X _ _ _) X.";
  LPCode "pred quadruple_2  i:quadruple A1 A2 A3 A4, o:A2.";
  LPCode "quadruple_2 (quadruple _ X _ _) X.";
  LPCode "pred quadruple_3  i:quadruple A1 A2 A3 A4, o:A3.";
  LPCode "quadruple_3 (quadruple _ _ X _) X.";
  LPCode "pred quadruple_4  i:quadruple A1 A2 A3 A4, o:A4.";
  LPCode "quadruple_4 (quadruple _ _ _ X) X.";

  MLData (quintuple (BuiltInData.poly "A") (BuiltInData.poly "B") (BuiltInData.poly "C") (BuiltInData.poly "D") (BuiltInData.poly "E"));

  LPCode "pred quintuple_1  i:quintuple A1 A2 A3 A4 A5, o:A1.";
  LPCode "quintuple_1 (quintuple X _ _ _ _) X.";
  LPCode "pred quintuple_2  i:quintuple A1 A2 A3 A4 A5, o:A2.";
  LPCode "quintuple_2 (quintuple _ X _ _ _) X.";
  LPCode "pred quintuple_3  i:quintuple A1 A2 A3 A4 A5, o:A3.";
  LPCode "quintuple_3 (quintuple _ _ X _ _) X.";
  LPCode "pred quintuple_4  i:quintuple A1 A2 A3 A4 A5, o:A4.";
  LPCode "quintuple_4 (quintuple _ _ _ X _) X.";
  LPCode "pred quintuple_5  i:quintuple A1 A2 A3 A4 A5, o:A5.";
  LPCode "quintuple_5 (quintuple _ _ _ _ X) X.";

  MLData (option (BuiltInData.poly "A"));

  MLData cmp;

  MLData BuiltInData.diagnostic;

  ]
;;

(** Standard lambda Prolog I/O built-in *********************************** *)

let io_builtins = let open BuiltIn in let open BuiltInData in let open Conversion in [

  LPDoc " == I/O builtins =====================================";

  LPDoc " -- I/O --";

  MLData (in_stream);

  MLData (out_stream);

  MLCode(Pred("open_in",
    In(string,     "FileName",
    Out(in_stream, "InStream",
    Easy           "opens FileName for input")),in_raw_ctx,
  (fun s _ ~depth ->
     try !:(open_in s,s)
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("open_out",
    In(string,      "FileName",
    Out(out_stream, "OutStream",
    Easy            "opens FileName for output")),in_raw_ctx,
  (fun s _ ~depth ->
     try !:(open_out s,s)
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("open_append",
    In(string,      "FileName",
    Out(out_stream, "OutStream",
    Easy            "opens FileName for output in append mode")),in_raw_ctx,
  (fun s _ ~depth ->
     let flags = [Open_wronly; Open_append; Open_creat; Open_text] in
     try !:(open_out_gen flags 0x664 s,s)
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("close_in",
    In(in_stream, "InStream",
    Easy          "closes input stream InStream"),in_raw_ctx,
  (fun (i,_) ~depth ->
     try close_in i
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("close_out",
    In(out_stream, "OutStream",
    Easy           "closes output stream OutStream"),in_raw_ctx,
  (fun (o,_) ~depth ->
     try close_out o
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("output",
    In(out_stream, "OutStream",
    In(string,     "Data",
    Easy           "writes Data to OutStream")),in_raw_ctx,
  (fun (o,_) s ~depth ->
     try output_string o s
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("flush",
    In(out_stream, "OutStream",
    Easy           "flush all output not yet finalized to OutStream"),in_raw_ctx,
  (fun (o,_) ~depth ->
     try flush o
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("input",
    In(in_stream, "InStream",
    In(int,       "Bytes",
    Out(string,   "Data",
    Easy          "reads Bytes from InStream"))),in_raw_ctx,
  (fun (i,_) n _ ~depth ->
     let buf = Bytes.make n ' ' in
     try
       let read = really_input i buf 0 n in
       let str = Bytes.sub buf 0 read in
       !:(Bytes.to_string str)
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("input_line",
    In(in_stream, "InStream",
    Out(string,   "Line",
    Easy          "reads a full line from InStream")),in_raw_ctx,
  (fun (i,_) _ ~depth ->
     try !:(input_line i)
     with
     | End_of_file -> !:""
     | Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("eof",
    In(in_stream, "InStream",
    Easy          "checks if no more data can be read from InStream"),in_raw_ctx,
  (fun (i,_) ~depth ->
     try
       let pos = pos_in i in
       let _ = input_char i in
       Pervasives.seek_in i pos;
       raise No_clause
     with
     | End_of_file -> ()
     | Sys_error msg -> error msg)),
  DocAbove);

  LPDoc " -- System --";

  MLCode(Pred("gettimeofday",
    Out(float, "T",
    Easy       "sets T to the number of seconds elapsed since 1/1/1970"),in_raw_ctx,
  (fun _ ~depth -> !:(Unix.gettimeofday ()))),
  DocAbove);

  MLCode(Pred("getenv",
    In(string,  "VarName",
    Out(option string, "Value",
    Easy      ("Like Sys.getenv"))),in_raw_ctx,
  (fun s _ ~depth ->
     try !:(Some (Sys.getenv s))
     with Not_found -> !: None)),
  DocAbove);

  MLCode(Pred("system",
    In(string, "Command",
    Out(int,   "RetVal",
    Easy       "executes Command and sets RetVal to the exit code")),in_raw_ctx,
  (fun s _ ~depth -> !:(Sys.command s))),
  DocAbove);

  LPDoc " -- Debugging --";

  MLCode(Pred("term_to_string",
    In(any,     "T",
    Out(string, "S",
    Easy        "prints T to S")),in_raw_ctx,
  (fun t _ ~depth ->
     let b = Buffer.create 1024 in
     let fmt = Format.formatter_of_buffer b in
     Format.fprintf fmt "%a" (RawPp.term depth) t ;
     Format.pp_print_flush fmt ();
       !:(Buffer.contents b))),
  DocAbove);

  ]
;;

(** Standard lambda Prolog built-in ************************************** *)

let lp_builtins = let open BuiltIn in let open BuiltInData in let open Conversion in [

  LPDoc "== Lambda Prolog builtins =====================================";

  LPDoc " -- Extra I/O --";

  MLCode(Pred("open_string",
    In(string,     "DataIn",
    Out(in_stream, "InStream",
    Easy           "opens DataIn as an input stream")),in_raw_ctx,
  (fun data _ ~depth ->
     try
       let filename, outch = Filename.open_temp_file "elpi" "tmp" in
       output_string outch data;
       close_out outch ;
       let v = open_in filename in
       Sys.remove filename ;
       !:(v,"<string>")
     with Sys_error msg -> error msg)),
  DocAbove);

  MLCode(Pred("lookahead",
    In(in_stream, "InStream",
    Out(string,   "NextChar",
    Easy          "peeks one byte from InStream")),in_raw_ctx,
  (fun (i,_) _ ~depth ->
     try
       let pos = pos_in i in
       let c = input_char i in
       Pervasives.seek_in i pos;
       !:(String.make 1 c)
     with
     | End_of_file -> !:""
     | Sys_error msg -> error msg)),
  DocAbove);

  LPDoc " -- Hacks --";

  MLCode(Pred("string_to_term",
    In(string, "S",
    Out(any,   "T",
    Full("parses a term T from S"))),in_raw_ctx,
  (fun s _ ~depth _ _ state ->
     try
       let loc = Ast.Loc.initial "(string_of_term)" in
       let t = Parse.goal loc s in
       let state, t = Quotation.term_at ~depth state t in
       state, !:t, []
     with
     | Parse.ParseError _ -> raise No_clause)),
  DocAbove);

  MLCode(Pred("readterm",
    In(in_stream, "InStream",
    Out(any,      "T",
    Full("reads T from InStream"))),in_raw_ctx,
  (fun (i,source_name) _ ~depth _ _ state ->
     try
       let loc = Ast.Loc.initial source_name in
       let strm = Stream.of_channel i in
       let t = Parse.goal_from_stream loc strm in
       let state, t = Quotation.term_at ~depth state t in
       state, !:t, []
     with
     | Sys_error msg -> error msg
     | Parse.ParseError _ -> raise No_clause)),
  DocAbove);

  LPCode "pred printterm i:out_stream, i:A.";
  LPCode "printterm S T :- term_to_string T T1, output S T1.";

  LPCode "pred read o:A.";
  LPCode "read S :- flush std_out, input_line std_in X, string_to_term X S.";

  ]
;;

(** ELPI specific built-in ************************************************ *)

let elpi_builtins = let open BuiltIn in let open BuiltInData in let open Conversion in [

  LPDoc "== Elpi builtins =====================================";

  MLCode(Pred("dprint",
    VariadicIn(any, "prints raw terms (debugging)"),in_raw_ctx,
  (fun args ~depth _ _ state ->
     Utils.printf "@[<hov 1>%a@]@\n%!"
       (RawPp.list (RawPp.Debug.term depth) " ") args ;
     state, ())),
  DocAbove);

  MLCode(Pred("print",
    VariadicIn(any,"prints terms"),in_raw_ctx,
  (fun args ~depth _ _ state ->
     Utils.printf "@[<hov 1>%a@]@\n%!"
       (RawPp.list (RawPp.term depth) " ") args ;
     state, ())),
  DocAbove);

  MLCode(Pred("counter",
    In (string,"Name",
    Out(int,   "Value",
    Easy       "reads the Value of a trace point Name")),in_raw_ctx,
  (fun s _ ~depth:_ -> !:(Trace_ppx_runtime.Runtime.get_cur_step s))),
  DocAbove);

  MLCode(Pred("rex_match",
    In(string, "Rex",
    In(string, "Subject",
    Easy      ("checks if Subject matches Rex. "^
               "Matching is based on OCaml's Str library"))),in_raw_ctx,
  (fun rex subj ~depth ->
     let rex = Str.regexp rex in
     if Str.string_match rex subj 0 then () else raise No_clause)),
  DocAbove);

  MLCode(Pred("rex_replace",
    In(string,  "Rex",
    In(string,  "Replacement",
    In(string,  "Subject",
    Out(string, "Out",
    Easy   ("Out is obtained by replacing all occurrences of Rex with "^
            "Replacement in Subject. See also OCaml's Str.global_replace"))))),in_raw_ctx,
  (fun rex repl subj _ ~depth ->
     let rex = Str.regexp rex in
     !:(Str.global_replace rex repl subj))),
  DocAbove);

   MLCode(Pred("quote_syntax",
     In(string, "FileName",
     In(string, "QueryText",
     Out(list (poly "A"), "QuotedProgram",
     Out(poly "A",        "QuotedQuery",
     Full    ("quotes the program from FileName and the QueryText. "^
              "See elpi-quoted_syntax.elpi for the syntax tree"))))),in_raw_ctx,
   (fun f s _ _ ~depth _ _ state ->
      let elpi, _ = Setup.init ~builtins:[BuiltIn.declare ~file_name:"(dummy)" []] ~basedir:Sys.(getcwd()) [] in
      try
        let ap = Parse.program ~elpi [f] in
        let loc = Ast.Loc.initial "(quote_syntax)" in
        let aq = Parse.goal loc s in
        let p = Compile.(program ~flags:default_flags ~elpi [ap]) in
        let q = API.Compile.query p aq in
        let state, qp, qq = Quotation.quote_syntax_runtime state q in
        state, !: qp +! qq, []
      with Parse.ParseError (_,m) | Compile.CompileError (_,m) ->
        Printf.eprintf "%s\n" m;
        raise No_clause)),
  DocAbove);

  MLData loc;
]
;;

(** ELPI specific NON-LOGICAL built-in *********************************** *)

let ctype = AlgebraicData.declare {
  AlgebraicData.ty = TyName "ctyp";
  doc = "Opaque ML data types";
  pp = (fun fmt cty -> Format.fprintf fmt "%s" cty);
  constructors = [
    K("ctype","",A(BuiltInData.string,N),B (fun x -> x), M (fun ~ok ~ko x -> ok x))  
  ]
}

let ty, pp, pp_doc, safe = OpaqueData.declare {
  OpaqueData.name = "safe";
  cname = "safe";
  pp = (fun fmt (id,l) ->
     Format.fprintf fmt "[safe %d: %a]" id
       (RawPp.list (fun fmt (t,d) -> RawPp.term d fmt t) ";") !l);
  compare = (fun (id1, _) (id2,_) -> Util.Int.compare id1 id2);
  hash = (fun (id,_) -> id);
  hconsed = false;
  doc = "Holds data across bracktracking; can only contain closed terms";
  constants = [];
}
let safe : 'c. ('a, #Conversion.ctx as 'c) Conversion.t = { Conversion.ty; pp; pp_doc;
  embed = (fun ~depth -> OpaqueData.embed safe ~depth);
  readback = (fun ~depth -> OpaqueData.readback safe ~depth);
}

let safeno = ref 0

let fresh_int = ref 0

(* factor the code of name and constant *)
let name_or_constant name condition = (); fun x out ~depth _ _ state ->
  let len = List.length out in
  if len != 0 && len != 2 then
    type_error (name^" only supports 1 or 3 arguments");
  state,
  match x with
  | NoData -> raise No_clause
  | Data x ->
      match look ~depth x with
      | Const n when condition n ->
          if out = [] then !: x +? None
          else !: x +! [Some x; Some mkNil]
      | App(n,y,ys) when condition n ->
          if out = [] then !: x +? None
          else !: x +! [Some (mkConst n); Some (list_to_lp_list (y::ys))]
      | UnifVar _ ->
          (* We build the application *)
          begin match out with
          | [] -> raise No_clause
          | [Data hd; Data args] ->
              begin match look ~depth hd, lp_list_to_list ~depth args with
              | Const n, [] when condition n ->
                  !: (mkConst n) +! [Some hd; Some args]
              | Const n, x :: xs when condition n ->
                  !: (mkApp n x xs) +! [Some hd; Some args]
              | _ -> raise No_clause end
          | _ -> raise No_clause
          end
      | _ -> raise No_clause
;;

let rec same_term ~depth t1 t2 =
  match look ~depth t1, look ~depth t2 with
  | UnifVar(b1,xs), UnifVar(b2,ys) -> FlexibleData.Elpi.equal b1 b2 && same_term_list ~depth xs ys
  | App(c1,x,xs), App(c2,y,ys) -> c1 == c2 && same_term ~depth x y && same_term_list ~depth xs ys
  | Const c1, Const c2 -> c1 == c2
  | Cons(x,xs), Cons(y,ys) -> same_term ~depth x y && same_term ~depth xs ys
  | Nil, Nil -> true
  | Lam x, Lam y -> same_term ~depth:(depth+1) x y
  | Builtin(c1,xs),Builtin(c2,ys) -> c1 == c2 && same_term_list ~depth xs ys
  | CData d1, CData d2 -> RawOpaqueData.equal d1 d2
  | _ -> false
and same_term_list ~depth xs ys =
  match xs, ys with
  | [], [] -> true
  | x::xs, y::ys -> same_term ~depth x y && same_term_list ~depth xs ys
  | _ -> false

let elpi_nonlogical_builtins = let open BuiltIn in let open BuiltInData in let open Conversion in [

  LPDoc "== Elpi nonlogical builtins =====================================";

  MLData ctype;

  MLCode(Pred("var",
    In(any,   "V",
    Easy       "checks if the term V is a variable"),in_raw_ctx,
  (fun t1 ~depth ->
     match look ~depth t1 with
     | UnifVar _ -> ()
     | _ -> raise No_clause)),
  DocAbove);

  MLCode(Pred("same_var",
    In(poly "A",   "V1",
    In(poly "A",   "V2",
    Easy       "checks if the two terms V1 and V2 are the same variable, ignoring the arguments of the variables")),in_raw_ctx,
  (fun t1 t2 ~depth ->
     match look ~depth t1, look ~depth t2 with
     | UnifVar(p1,_), UnifVar (p2,_) when FlexibleData.Elpi.equal p1 p2 -> ()
     | _,_ -> raise No_clause)),
  DocAbove);

  MLCode(Pred("same_term",
    In(poly "A",   "T1",
    In(poly "A",   "T2",
    Easy {|checks if the two terms T1 and T2 are syntactically equal (no unification). It behaves differently than same_var since it recursively compares the arguments of the variables|})),in_raw_ctx,
  (fun t1 t2 ~depth ->
     if same_term ~depth t1 t2 then () else raise No_clause)),
  DocAbove);

  LPCode {|
% Infix notation for same_term
pred (==) i:A, i:A.
X == Y :- same_term X Y.
|};

  MLCode(Pred("cmp_term",
    In(any, "A",
    In(any, "B",
    Out(cmp,"Cmp",
    Easy "Compares A and B. Only works if A and B are ground."))),in_raw_ctx,
  (fun t1 t2 _ ~depth -> !: (cmp_term ~depth t1 t2))),
  DocAbove);

  MLCode(Pred("name",
    InOut(ioarg_any, "T",
    VariadicInOut(ioarg any,"checks if T is a eigenvariable. When used with tree arguments it relates an applied name with its head and argument list.")),in_raw_ctx,
  (name_or_constant "name" (fun x -> x >= 0))),
  DocAbove);

  MLCode(Pred("constant",
    InOut(ioarg_any, "T",
    VariadicInOut(ioarg any,"checks if T is a (global) constant.  When used with tree arguments it relates an applied constant with its head and argument list.")),in_raw_ctx,
  (name_or_constant "constant" (fun x -> x < 0))),
  DocAbove);

  MLCode(Pred("names",
    Out(list any, "list of eigenvariables in order of age (young first)",
    Easy           "generates the list of eigenvariable"),in_raw_ctx,
  (* XXX 4.06: (fun _ ~depth -> !:(List.init depth mkConst))), *)
  (fun _ ~depth ->
     let rec list_init i n f =
       if i >= n then [] else
       f i :: list_init (i+1) n f in
     !:(list_init 0 depth mkConst))),
  DocNext);

  MLCode(Pred("occurs",
    In(any, "a constant (global or eigenvariable)",
    In(any, "a term",
    Easy     "checks if the constant occurs in the term")),in_raw_ctx,
  (fun t1 t2 ~depth ->
     let occurs_in t2 t =
       match look ~depth t with
       | Const n -> occurs n depth t2
       | _ -> error "The second argument of occurs must be a constant" in
     if occurs_in t2 t1 then () else raise No_clause)),
  DocNext);

  MLCode(Pred("closed_term",
    Out(any, "T",
    Full ("unify T with a variable that has no eigenvariables in scope")),in_raw_ctx,
  (fun _ ~depth _ _ state ->
      let state, k = FlexibleData.Elpi.make state in
      state, !:(mkUnifVar k ~args:[] state), [])),
  DocAbove);

  MLCode(Pred("ground_term",
    In(any, "T",
    Easy ("Checks if T contains unification variables")),in_raw_ctx,
  (fun t ~depth -> check_ground ~depth t)),
  DocAbove);

  MLCode(Pred("is_cdata",
    In(any,     "T",
    Out(ctype,  "Ctype",
    Easy        "checks if T is primitive of type Ctype, eg (ctype \"int\")")),in_raw_ctx,
  (fun t _ ~depth ->
     match look ~depth t with
     | CData n -> !:(RawOpaqueData.name n)
     | _ -> raise No_clause)),
  DocAbove);

  LPCode "pred primitive? i:A, i:string.";
  LPCode "primitive? X S :- is_cdata X (ctype S).";

  MLCode(Pred("new_int",
     Out(int, "N",
     Easy     "unifies N with a different int every time it is called. Values of N are guaranteed to be incresing."),in_raw_ctx,
   (fun _ ~depth ->
      incr fresh_int;
      if !fresh_int < 0 then anomaly "new_int: reached max_int";
      !: !fresh_int)),
  DocAbove);

  MLData safe;

   MLCode(Pred("new_safe",
     Out(safe, "Safe",
     Easy      "creates a safe: a store that persists across backtracking"),in_raw_ctx,
   (fun _ ~depth -> incr safeno; !:(!safeno,ref []))),
  DocAbove);

   MLCode(Pred("stash_in_safe",
     In(safe,  "Safe",
     In(closed "A",   "Data",
     Easy      "stores Data in the Safe")),in_raw_ctx,
   (fun (_,l) t ~depth -> l := t :: !l)),
  DocAbove);

   MLCode(Pred("open_safe",
     In(safe, "Safe",
     Out(list (closed "A"), "Data",
     Easy          "retrieves the Data stored in Safe")),in_raw_ctx,
   (fun (_,l) _ ~depth -> !:(List.rev !l))),
  DocAbove);

  LPCode {|
% [if C T E] picks the first success of C then runs T (never E).
% if C has no success it runs E.
pred if i:prop, i:prop, i:prop.
if B T _ :- B, !, T.
if _ _ E :- E.  |};

  MLCode(Pred("random.init",
     In(int, "Seed",
     Easy     "Initialize OCaml's PRNG with the given Seed"),in_raw_ctx,
   (fun seed ~depth:_ -> Random.init seed)),
  DocAbove);

  MLCode(Pred("random.self_init",
     Easy     "Initialize OCaml's PRNG with some seed",in_raw_ctx,
   (fun ~depth:_ -> Random.self_init ())),
  DocAbove);

  MLCode(Pred("random.int",
     In(int, "Bound",
     Out(int, "N",
     Easy     "unifies N with a random int between 0 and Bound (excluded)")),in_raw_ctx,
   (fun bound _ ~depth -> !: (Random.int bound))),
  DocAbove);

]
;;

let elpi_stdlib_src = let open BuiltIn in let open BuiltInData in [

  LPCode Builtin_stdlib.code

]

let ocaml_set ~name (type a)
   (alpha : (a,Conversion.ctx) Conversion.t) (module Set : Util.Set.S with type elt = a) =

let ty, pp, pp_doc, set = OpaqueData.declare {
  OpaqueData.name;
  cname = name;
  doc = "";
  pp = (fun fmt m -> Format.fprintf fmt "%a" Set.pp m );
  compare = (fun m1 m2 -> Set.compare m1 m2);
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
} in
let set : (Set.t, #Conversion.ctx as 'c) Conversion.t = { Conversion.ty; pp; pp_doc;
  embed = (fun ~depth -> OpaqueData.embed set ~depth);
  readback = (fun ~depth -> OpaqueData.readback set ~depth);
} in

let open BuiltIn in let open BuiltInData in let open Conversion in

[
  LPCode ("kind "^name^" type.");

  MLCode(Pred(name^".empty",
    Out(set,"A",
    Easy "The empty set"),in_raw_ctx,
    (fun _ ~depth -> !: Set.empty)),
  DocAbove);

  MLCode(Pred(name^".mem",
    In(alpha,"Elem",
    In(set,"A",
    Easy "Checks if Elem is in a")),in_raw_ctx,
    (fun s m ~depth ->
      if Set.mem s m then () else raise No_clause)),
  DocAbove);

  MLCode(Pred(name^".add",
    In(alpha,"Elem",
    In(set,"A",
    Out(set,"B",
    Easy "B is A union {Elem}"))),in_raw_ctx,
    (fun s m _ ~depth -> !: (Set.add s m))),
  DocAbove);

  MLCode(Pred(name^".remove",
    In(alpha,"Elem",
    In(set,"A",
    Out(set,"B",
    Easy "B is A \ {Elem}"))),in_raw_ctx,
    (fun s m _ ~depth -> !: (Set.remove s m))),
  DocAbove);

    MLCode(Pred(name^".union",
    In(set,"A",
    In(set,"B",
    Out(set,"X",
    Easy "X is A union B"))),in_raw_ctx,
    (fun a b _ ~depth -> !: (Set.union a b))),
    DocAbove);

   MLCode(Pred(name^".inter",
    In(set,"A",
    In(set,"B",
    Out(set,"X",
    Easy "X is A intersection B"))),in_raw_ctx,
    (fun a b _ ~depth -> !: (Set.inter a b))),
  DocAbove);

  MLCode(Pred(name^".diff",
    In(set,"A",
    In(set,"B",
    Out(set,"X",
    Easy "X is A \ B"))),in_raw_ctx,
    (fun a b _ ~depth -> !: (Set.diff a b))),
  DocAbove);

  MLCode(Pred(name^".equal",
    In(set,"A",
    In(set,"B",
    Easy "tests A and B for equality")),in_raw_ctx,
    (fun a b ~depth -> if Set.equal a b then () else raise No_clause)),
  DocAbove);

  MLCode(Pred(name^".subset",
    In(set,"A",
    In(set,"B",
    Easy "tests if A is a subset of B")),in_raw_ctx,
    (fun a b ~depth -> if Set.subset a b then () else raise No_clause)),
  DocAbove);

  MLCode(Pred(name^".elements",
    In(set,"M",
    Out(list alpha,"L",
    Easy "L is M transformed into list")),in_raw_ctx,
    (fun m _ ~depth -> !: (Set.elements m))),
  DocAbove);

  MLCode(Pred(name^".cardinal",
    In(set,"M",
    Out(int,"N",
    Easy "N is the number of elements of M")),in_raw_ctx,
    (fun m _ ~depth -> !: (Set.cardinal m))),
  DocAbove);
]
;;

let ocaml_map ~name (type a)
   (alpha : (a,Conversion.ctx) Conversion.t) (module Map : Util.Map.S with type key = a) =

let closed_A = BuiltInData.closed "A" in

let ty, pp, pp_doc, map = OpaqueData.declare {
  OpaqueData.name;
  cname = name;
  doc = "";
  pp = (fun fmt m -> Format.fprintf fmt "%a" (Map.pp closed_A.pp) m );
  compare = (fun m1 m2 -> Map.compare Pervasives.compare m1 m2);
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
} in
let map a = {
  Conversion.ty = Conversion.(TyApp(name,TyName a,[]));
  pp; pp_doc;
  embed = (fun ~depth -> OpaqueData.embed map ~depth);
  readback = (fun ~depth -> OpaqueData.readback map ~depth);
} in

let open BuiltIn in let open BuiltInData in let open Conversion in

[
  LPDoc ("CAVEAT: the type parameter of "^name^" must be a closed term");
  LPCode ("kind "^name^" type -> type.");

  MLCode(Pred(name^".empty",
    Out(map "A","M",
    Easy "The empty map"),in_raw_ctx,
    (fun _ ~depth -> !: Map.empty)),
  DocAbove);

  MLCode(Pred(name^".mem",
    In(alpha,"S",
    In(map "A","M",
    Easy "Checks if S is bound in M")),in_raw_ctx,
    (fun s m ~depth ->
      if Map.mem s m then () else raise No_clause)),
  DocAbove);

  MLCode(Pred(name^".add",
    In(alpha,"S",
    In(closed_A,"V",
    In(map "A","M",
    Out(map "A","M1",
    Easy "M1 is M where V is bound to S")))),in_raw_ctx,
    (fun s l m _ ~depth -> !: (Map.add s l m))),
  DocAbove);

  MLCode(Pred(name^".remove",
    In(alpha,"S",
    In(map "A","M",
    Out(map "A","M1",
    Easy "M1 is M where S is unbound"))),in_raw_ctx,
    (fun s m _ ~depth -> !: (Map.remove s m))),
  DocAbove);

  MLCode(Pred(name^".find",
    In(alpha,"S",
    In(map "A","M",
    Out(closed_A,"V",
    Easy "V is the binding of S in M"))),in_raw_ctx,
    (fun s m _ ~depth ->
       try !: (Map.find s m)
       with Not_found -> raise No_clause)),
  DocAbove);

  MLCode(Pred(name^".bindings",
    In(map "A","M",
    Out(list (pair alpha (closed_A)),"L",
    Easy "L is M transformed into an associative list")),in_raw_ctx,
    (fun m _ ~depth -> !: (Map.bindings m))),
  DocAbove);

]
;;

module LocMap : Util.Map.S with type key = Ast.Loc.t = Util.Map.Make(Ast.Loc)
module LocSet : Util.Set.S with type elt = Ast.Loc.t = Util.Set.Make(Ast.Loc)

let elpi_map =  let open BuiltIn in let open BuiltInData in [

    LPCode Builtin_map.code

]

let elpi_set =  let open BuiltIn in let open BuiltInData in [

    LPCode Builtin_set.code

]

let elpi_stdlib =
  elpi_stdlib_src @
  ocaml_map ~name:"std.string.map" BuiltInData.string (module Util.StrMap) @
  ocaml_map ~name:"std.int.map"    BuiltInData.int    (module Util.IntMap) @
  ocaml_map ~name:"std.loc.map"    BuiltInData.loc    (module LocMap) @
  ocaml_set ~name:"std.string.set" BuiltInData.string (module Util.StrSet) @
  ocaml_set ~name:"std.int.set"    BuiltInData.int    (module Util.IntSet) @
  ocaml_set ~name:"std.loc.set"    BuiltInData.loc    (module LocSet) @
  []
;;

let std_declarations =
  core_builtins @ io_builtins @ lp_builtins @ elpi_builtins @ elpi_nonlogical_builtins @ elpi_stdlib @ elpi_map @ elpi_set

let std_builtins =
  BuiltIn.declare ~file_name:"builtin.elpi" std_declarations


let default_checker () =
  let elpi, _ = API.Setup.init ~builtins:[std_builtins] ~basedir:(Sys.getcwd ()) [] in
  let ast = API.Parse.program_from_stream ~elpi (API.Ast.Loc.initial "(checker)") (Stream.of_string Builtin_checker.code) in
  API.Compile.program ~flags:API.Compile.default_flags ~elpi [ast]
