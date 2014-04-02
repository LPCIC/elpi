(* Immutable array *)

module IA = struct

  include BIA

  let append v1 v2 =
    let len1 = BIA.len v1 in
    BIA.init (len1 + BIA.len v2)
      (fun i -> if i < len1 then BIA.get i v1 else BIA.get (i-len1) v2)

  let cons t v =
    BIA.init (BIA.len v+1) (fun i -> if i = 0 then t else BIA.get (i-1) v)

end

(* External, user defined, datatypes *)
module C : sig

  type t
  type ty
  type data = {
    t : t;
    ty : ty;
  }

  val declare : ('a -> string) -> ('a -> 'a -> bool) -> 'a -> data
  
  val print : data -> string
  val equal : data -> data -> bool

end = struct (* {{{ *)

type t = Obj.t
type ty = int

type data = {
  t : Obj.t;
  ty : int
}

module M = Int.Map
let m : ((data -> string) * (data -> data -> bool)) M.t ref = ref M.empty

let cget x = Obj.obj x.t
let print x = fst (M.find x.ty !m) x
let equal x y = x.ty = y.ty && snd (M.find x.ty !m) x y

let fresh_tid =
  let tid = ref 0 in
  fun () -> incr tid; !tid

let declare print cmp =
  let tid = fresh_tid () in
  m := M.add tid ((fun x -> print (cget x)),
                  (fun x y -> cmp (cget x) (cget y))) !m;
  fun v -> { t = Obj.repr v; ty = tid }

end (* }}} *)

let on_buffer f x =
  let b = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer b in
  f fmt x;
  Format.pp_print_flush fmt ();
  Buffer.contents b

module LP = struct

type var = int
type level = int
type name = string

type kind_of_data =
  | Uv of var * level
  | Con of name * level
  | DB of int
  | Bin of int * data
  | Tup of data IA.t
  | Ext of C.data
and data = kind_of_data
let look x = x
let mkUv v l = Uv(v,l)
let mkCon n l = Con(n,l)
let mkDB i = DB i
let mkBin n t = Bin(n,t)
let mkTup xs = Tup xs
let mkExt x = Ext x
let kool x = x

let small_digit = function
  | 0 -> "⁰" | 1 -> "¹" | 2 -> "²" | 3 -> "³" | 4 -> "⁴" | 5 -> "⁵"
  | 6 -> "⁶" | 7 -> "⁷" | 8 -> "⁸" | 9 -> "⁹" | _ -> assert false

let rec digits_of n =
  let n, r = n / 10, n mod 10 in
  r :: if n > 0 then digits_of n else []

let string_of_level lvl = if !Trace.debug then "^" ^ string_of_int lvl
  else if lvl = 0 then ""
  else String.concat "" (List.map small_digit (digits_of lvl))

let pr_cst x lvl = x ^ if !Trace.debug then string_of_level lvl else ""
let pr_var x lvl = "X" ^ string_of_int x ^ string_of_level lvl

let mkBin n t = if n = 0 then t else Bin(n,t)

let mkApp t v start stop =
  if start = stop then t else
  match t with
  | Tup xs -> Tup(IA.append xs (IA.sub start (stop-start) v))
  | _ -> Tup(IA.cons t (IA.sub start (stop-start) v))

let fixTup xs =
  match IA.get 0 xs with
  | Tup ys -> Tup (IA.append ys (IA.tl xs))
  | _ -> Tup xs

let rec equal a b = match a,b with
 | Uv (x,_), Uv (y,_) -> x = y
 | Con (x,_), Con (y,_) -> x = y
 | DB x, DB y -> x = y
 | Bin (n1,x), Bin (n2,y) -> n1 = n2 && equal x y
 | Tup xs, Tup ys -> IA.for_all2 equal xs ys
 | Ext x, Ext y -> C.equal x y
 | _ -> false

let rec fresh_names k = function
  | 0 -> []
  | n -> ("w" ^ string_of_int k) :: fresh_names (k+1) (n-1)

let rec iter_sep spc pp = function
  | [] -> ()
  | [x] -> pp x
  | x::tl -> pp x; spc (); iter_sep spc pp tl

let isBin = function Bin _ -> true | _ -> false

let prf_data ctx fmt t =
  let module P = Format in
  let rec print ?(pars=false) ctx = function
    | Bin (n,x) ->
       P.pp_open_hovbox fmt 2;
       let names = fresh_names (List.length ctx) n in
       if pars then P.pp_print_string fmt "(";
       P.pp_print_string fmt (String.concat "\\ " names ^ "\\");
       P.pp_print_space fmt ();
       print (List.rev names @ ctx) x;
       if pars then P.pp_print_string fmt ")";
       P.pp_close_box fmt ()
    | DB x -> P.pp_print_string fmt 
        (try (if !Trace.debug then "'" else "") ^List.nth ctx (x-1)
        with Failure _ | Invalid_argument _ ->
          "_" ^ string_of_int (x-List.length ctx))
    | Con (x,lvl) -> P.pp_print_string fmt (pr_cst x lvl)
    | Uv (x,lvl) -> P.pp_print_string fmt (pr_var x lvl)
    | Tup xs ->
        P.pp_open_hovbox fmt 2;
        if pars then P.pp_print_string fmt "(";
        iter_sep (P.pp_print_space fmt) (print ~pars:true ctx) (IA.to_list xs);
        if pars then P.pp_print_string fmt ")";
        P.pp_close_box fmt ()
    | Ext x ->
        P.pp_open_hbox fmt ();
        P.pp_print_string fmt (C.print x);
        P.pp_close_box fmt ()
  in
    print ctx t
let string_of_data ?(ctx=[]) t = on_buffer (prf_data ctx) t


let rec fold f x a = match x with
  | (DB _ | Con _ | Uv _ | Ext _) as x -> f x a
  | Bin (_,x) -> fold f x a
  | Tup xs -> IA.fold (fold f) xs a

let rec map f = function
  | (DB _ | Con _ | Uv _ | Ext _) as x -> f x
  | Bin (ns,x) -> Bin(ns, map f x)
  | Tup xs -> Tup(IA.map (map f) xs)

let max_uv x a = match x with Uv (i,_) -> max a i | _ -> a

let rec fold_map f x a = match x with
  | (DB _ | Con _ | Uv _ | Ext _) as x -> f x a
  | Bin (n,x) -> let x, a = fold_map f x a in Bin(n,x), a
  | Tup xs -> let xs, a = IA.fold_map (fold_map f) xs a in Tup xs, a
 
(* PROGRAM *)
type program = clause list
and clause = int * head * premise list (* level, maxuv, head, premises *)
and head = data
and premise =
  | Atom of data
  | Impl of data * premise
  | Pi of name * premise
and goal = premise

let rec map_premise f = function
  | Atom x -> Atom(f x)
  | Impl(x,y) -> Impl(f x, map_premise f y)
  | Pi(n,x) -> Pi(n, map_premise f x)

let rec fold_premise f x a = match x with
  | Atom x -> f x a
  | Impl(x,y) -> fold_premise f y (f x a)
  | Pi(_,x) -> fold_premise f x a

let rec fold_map_premise f p a = match p with
  | Atom x -> let x, a = f x a in Atom x, a
  | Impl(x,y) -> let x, a = f x a in
                 let y, a = fold_map_premise f y a in
                 Impl(x,y), a
  | Pi(n,y) -> let y, a = fold_map_premise f y a in Pi(n, y), a

let rec number = lexer [ '0'-'9' number | ]
let rec ident =
  lexer [ [ 'a'-'z' | '\'' | '_' | '0'-'9' ] ident | '^' '0'-'9' number | ]

let lvl_name_of s =
  match Str.split (Str.regexp_string "^") s with
  | [ x ] -> x, 0
  | [ x;l ] -> x, int_of_string l
  | _ -> raise (Token.Error ("<name> ^ <number> expected.  Got: " ^ s))

let tok = lexer
  [ [ 'A'-'Z' ] ident -> "UVAR", $buf 
  | [ 'a'-'z' ] ident -> "CONSTANT", $buf
  | [ '_' '0'-'9' ] number -> "REL", $buf
  | [ ":-" ] -> "ENTAILS",$buf
  | [ ',' ] -> "COMMA",","
  | [ '.' ] -> "FULLSTOP","."
  | [ '\\' ] -> "BIND","\\"
  | [ '/' ] -> "BIND","/"
  | [ '(' ] -> "LPAREN","("
  | [ ')' ] -> "RPAREN",")"
  | [ "==>" ] -> "IMPL","==>"
]

let spy f s = if !Trace.debug then begin
  Printf.eprintf "<- %s\n"
    (match Stream.peek s with None -> "EOF" | Some x -> String.make 1 x);
  let t, v as tok = f s in
  Printf.eprintf "-> %s = %s\n" t v;
  tok
  end else f s

let rec foo c = parser
  | [< ' ( ' ' | '\n' ); s >] -> foo c s
  | [< '( '%' ); s >] -> comment c s
  | [< s >] ->
       match spy (tok c) s with
       | "CONSTANT","pi" -> "PI", "pi"
       | x -> x
and comment c = parser
  | [< '( '\n' ); s >] -> foo c s
  | [< '_ ; s >] -> comment c s

open Plexing

let lex_fun s =
  (Stream.from (fun _ -> Some (foo Lexbuf.empty s))), (fun _ -> Ploc.dummy)

let tok_match (s1,_) = (); function
  | (s2,v) when s1=s2 ->
      if !Trace.debug then Printf.eprintf "%s = %s = %s\n" s1 s2 v;
      v
  | (s2,v) ->
      if !Trace.debug then Printf.eprintf "%s <> %s = %s\n" s1 s2 v;
      raise Stream.Failure

let lex = {
  tok_func = lex_fun;
  tok_using = (fun _ -> ());
  tok_removing = (fun _ -> ());
  tok_match = tok_match;
  tok_text = (function (s,_) -> s);
  tok_comm = None;
}

let g = Grammar.gcreate lex
let lp = Grammar.Entry.create g "lp"
let goal = Grammar.Entry.create g "goal"
let atom = Grammar.Entry.create g "atom"

let uvmap = ref []
let conmap = ref []
let reset () = uvmap := []; conmap := []
let top_uv () = List.length !uvmap

let get_uv u =
  if List.mem_assoc u !uvmap then List.assoc u !uvmap
  else
    let n = List.length !uvmap in
    uvmap := (u,n) :: !uvmap;
    n
let check_con n l =
  try
    let l' = List.assoc n !conmap in
    if l <> l' then
      raise (Token.Error ("Constant "^n^" used at different levels"))
  with Not_found -> conmap := (n,l) :: !conmap

let rec binders c n = function
    | Con(c',_) when c = c' -> DB n
    | (Con _ | Uv _ | Ext _ | DB _) as x -> x
    | Bin(w,t) -> Bin(w,binders c (n+w) t)
    | Tup xs -> Tup (IA.map (binders c n) xs)
and binders_premise c n = function
    | Pi(c,t) -> Pi(c,binders_premise c (n+1) t)
    | Atom t -> Atom(binders c n t)
    | Impl(a,t) -> Impl(binders c n a, binders_premise c n t)

EXTEND
  GLOBAL: lp goal atom;
  lp: [ [ cl = LIST1 clause -> cl ] ];
  goal : [ [ g = atom; FULLSTOP -> Atom g ] ];
  clause :
    [ [ hd = atom;
        hyps =
          [ ENTAILS; hyps = LIST1 premise SEP COMMA; FULLSTOP -> hyps
          | FULLSTOP -> [] ] ->
              let top = top_uv () in reset ();
              top, hd, hyps ] ];
  atom :
    [ "1"
      [ hd = atom LEVEL "2"; args = LIST0 atom LEVEL "2" ->
          if args = [] then hd else Tup (IA.of_list (hd :: args)) ]
    | "2" 
      [ [ c = CONSTANT; b = OPT [ BIND; a = atom LEVEL "1" -> a ] ->
          let c, lvl = lvl_name_of c in
          match b with
          | None -> check_con c lvl; Con(c,lvl)
          | Some b ->  Bin(1,binders c 1 b) ]
      | [ u = UVAR -> let u, lvl = lvl_name_of u in Uv(get_uv u,lvl) ]
      | [ i = REL -> DB(int_of_string (String.sub i 1 (String.length i - 1))) ]
      | [ LPAREN; a = atom LEVEL "1"; RPAREN -> a ] ]
    ];
  premise :
    [ [ a = atom; next = OPT [ IMPL; p = premise -> p ] ->
         match next with
         | None -> Atom a
         | Some p -> Impl (a,p) ]
    | [ PI; c = CONSTANT; BIND; p = premise -> Pi(c, binders_premise c 1 p) ]
    ];
END

let parse e s =
  reset ();
  try Grammar.Entry.parse e (Stream.of_string s)
  with Ploc.Exc(l,(Token.Error msg | Stream.Error msg)) ->
    let last = Ploc.last_pos l in
    let ctx_len = 10 in
    let ctx =
      let start = max 0 (last - ctx_len) in
      let len = min (String.length s - start) ctx_len in
      "..." ^ String.sub s start len in
    raise (Stream.Error(Printf.sprintf "%s: %s" ctx msg))
  | Ploc.Exc(_,e) -> raise e

let parse_program s : program = parse lp s 
let parse_goal s : goal = parse goal s
let parse_data s : data = parse atom s

let rec prf_premise ctx fmt = function
  | Atom p -> prf_data ctx fmt p
  | Pi (x,p) ->
       Format.pp_open_hvbox fmt 2;
       Format.pp_print_string fmt ("pi "^x^"\\");
       Format.pp_print_space fmt ();
       prf_premise (x::ctx) fmt p;
       Format.pp_close_box fmt ()
  | Impl (x,p) ->
       Format.pp_open_hvbox fmt 2;
       prf_data ctx fmt x;
       Format.pp_print_space fmt ();
       Format.pp_open_hovbox fmt 0;
       Format.pp_print_string fmt "==> ";
       prf_premise ctx fmt p;
       Format.pp_close_box fmt ();
       Format.pp_close_box fmt ()
let string_of_premise p = on_buffer (prf_premise []) p
let string_of_goal = string_of_premise
let prf_goal = prf_premise []

let string_of_head = string_of_data

let prf_clause fmt (_, hd, hyps) =
  Format.pp_open_hvbox fmt 2;
  prf_data [] fmt hd;
  if hyps <> [] then begin
    Format.pp_print_space fmt ();
    Format.pp_print_string fmt ":- ";
  end;
  Format.pp_open_hovbox fmt 0;
  iter_sep
    (fun () -> Format.pp_print_string fmt ",";Format.pp_print_space fmt ())
    (prf_premise [] fmt) hyps;
  Format.pp_print_string fmt ".";
  Format.pp_close_box fmt ();
  Format.pp_close_box fmt ()

let string_of_clause c = on_buffer prf_clause c

let prf_program fmt p =
  Format.pp_open_vbox fmt 0;
  iter_sep (Format.pp_print_space fmt) (prf_clause fmt) p;
  Format.pp_close_box fmt ()
let string_of_program p = on_buffer prf_program p

end

open LP

(* LP.Uv |-> data mapping *)
module Subst = struct (* {{{ *)

type subst = { assign : data Int.Map.t; top_uv : int }
let empty n = { assign = Int.Map.empty; top_uv = n }

let last_sub_lookup = ref (DB 0)
let in_sub i { assign = assign } =
  try last_sub_lookup := Int.Map.find i assign; true
  with Not_found -> false
let set_sub i t s = { s with assign = Int.Map.add i t s.assign }

let rec iter_sep spc pp = function
  | [] -> ()
  | [x] -> pp x
  | x::tl -> pp x; spc (); iter_sep spc pp tl

let prf_subst fmt s =
  Format.pp_open_hovbox fmt 2;
  Format.pp_print_string fmt "{ ";
  iter_sep
    (fun () -> Format.pp_print_string fmt ";";Format.pp_print_space fmt ())
    (fun (i,t) ->
       Format.pp_open_hvbox fmt 0;
       Format.pp_print_string fmt (pr_var i 0);
       Format.pp_print_space fmt ();
       Format.pp_print_string fmt ":= ";
       prf_data [] fmt t;
       Format.pp_close_box fmt ())
    (Int.Map.bindings s.assign);
  Format.pp_print_string fmt " }";
  Format.pp_close_box fmt ()
let string_of_subst s = on_buffer prf_subst s

let apply_subst s t =
  let rec subst = function
    | Uv(i,_) when in_sub i s -> map subst !last_sub_lookup
    | x -> x in
  map subst t
let apply_subst_goal s = function
  | Atom t -> Atom(apply_subst s t)
  | _ -> assert false

let refresh_uv depth s x =
  map (function Uv(i,_) -> Uv(s.top_uv + i,depth) | x -> x) x

let top s = s.top_uv
let set_top i s = { s with top_uv = s.top_uv + i + 1 }

let fresh_uv lvl s = Uv(s.top_uv,lvl), { s with top_uv = s.top_uv + 1 }

end (* }}} *)

open Subst

(* beta reduction, whd, and nf (for tests) *) 
module Red = struct (* {{{ *)

open LP

let rec lift n k = function
  | Uv _ as x -> x
  | Con _ as x -> x
  | DB m when m > n -> DB (m+k)
  | DB _ as x -> x
  | Bin (ns,t) as x ->
      let t' = lift (n+ns) k t in
      if t == t' then x else Bin(ns,t')
  | Tup xs as x ->
      let xs' = IA.map (lift n k) xs in
      if xs' == xs then x else Tup xs'
  | Ext _ as x -> x
let lift ?(from=0) k t = if k = 0 then t else lift from k t

(* DB i := v.(start + len - i) *)
let rec beta depth t start len v =
  match t with
  | (Con _ | Ext _ | Uv _) as x -> x
  | DB m when m > depth && m - depth <= len ->
      lift depth (IA.get (start + len - (m - depth)) v)
  | DB m when m > depth -> DB (m - len)
  | DB _ as x -> x
  | Tup xs -> Tup(IA.map (fun t -> beta depth t start len v) xs)
  | Bin(ns,b) -> Bin(ns,beta (depth+ns) b start len v)

let rec whd s t =
  match t with
  | (Ext _ | Con _ | DB _ | Bin _) as x -> x, s
  | Uv (i,_) when in_sub i s ->
      let t = !last_sub_lookup in
      let t', s = whd s t in
      t', if t == t' then s else set_sub i t' s
  | Uv _ as x -> x, s
  | Tup v as x ->
      let hd = IA.get 0 v in
      let hd', s = whd s hd in
      match hd' with
      | Bin (n_lam,b) ->
        let n_args = IA.len v - 1 in
        if n_lam = n_args then
          whd s (beta 0 b 1 n_args v)
        else if n_lam < n_args then
          whd s (mkApp (beta 0 b 1 n_lam v) v (n_lam+1) (n_args+1))
        else
          let diff = n_lam - n_args in
          Bin(diff, beta diff b 1 n_args v), s
      | _ ->
          if hd == hd' then x, s
          else mkApp hd' (IA.tl v) 0 (IA.len v-1), s
          
let rec nf s = function
  | (Ext _ | Con _ | DB _) as x -> x
  | Bin(n,t) -> Bin(n,nf s t)
  | (Tup _ | Uv _) as x ->
      match fst(whd s x) with
      | Tup xs -> Tup(IA.map (nf s) xs)
      | y -> if y == x then y else nf s y

end (* }}} *)

open Red

(* vim:set foldmethod=marker: *)
