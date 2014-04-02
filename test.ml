open Lprun
open Lpdata

let toa x = LP.Tup(IA.of_array x)

module Coq = struct

type term =
  | Rel       of int
  | Var       of string
  | Evar      of int * term array
  | Sort      of bool
  | Cast      of term * term
  | Prod      of string * term * term
  | Lambda    of string * term * term
(*   | LetIn     of string * term * term * term *)
  | App       of term * term array
  | Const     of string
(*
  | Ind       of string
  | Construct of string
*)
(*   | Case      of term * term * term array *)
(*   | Fix       of (string * int * term * term) array *)

let quote x = "\""^x^"\""
let sob = function true -> "Type" | _ -> "Prop"

let cVar : string -> C.data = C.declare quote (=)
let of_Var s = LP.Ext (cVar s)

let cSort : bool -> C.data =
  C.declare (fun x -> quote (sob x)) (=)
let of_Sort s = LP.Ext (cSort s)

let cName : string -> C.data = C.declare quote (=)
let of_Name s = LP.Ext (cName s)



let app  = LP.Con ("app", 0)
let cast = LP.Con ("cast",0)
let prod = LP.Con ("prod",0)
let lam  = LP.Con ("lam", 0)
let hole = LP.Con ("hole",0)

(* module M = Map.Make(struct type t = int let compare = compare end) *)


let embed t (*sigma*) =
(*   let s = ref M.empty in *)
  let rec aux = function
  | Rel n -> LP.DB n
  | Var s -> of_Var s
  | Evar (i,ls) -> hole 
  (*aux_app (Tup [| ginst; M.find i s; aux (sigma i) |]) ls*)
  | Sort s -> of_Sort s
  | Cast(t,ty) -> toa [|cast; aux t; aux ty|]
  | Prod(n,ty,t) ->  toa [|prod; of_Name n; aux ty; LP.Bin(1,aux t) |]
  | Lambda(n,ty,t) ->  toa [|lam; of_Name n; aux ty; LP.Bin(1,aux t) |]
  | App(hd,args) -> aux_app (aux hd) args
  | Const n -> of_Name n
  and aux_app hd args =
     let len_args = Array.length args in
     if len_args = 0 then hd else
     let a = Array.create (len_args + 2) (LP.DB 0) in
     a.(0) <- app; a.(1) <- hd;
     for i = 0 to len_args - 1 do a.(i+2) <- aux args.(i); done;
     toa a
  in
    aux t

end

let cint : int -> C.data = C.declare string_of_int (=)
let of_int n = LP.Ext (cint n)

let clist : C.data list -> C.data =
  C.declare
    (fun l -> "[" ^ String.concat "; " (List.map C.print l) ^ "]")
    (List.for_all2 C.equal)
let of_list l = LP.Ext (clist l)

let test_IA () =
  let t = IA.of_array [| 1; 2; 3; 4; 5 |] in
  assert(t = IA.append (IA.sub 0 1 t) (IA.tl t));
  assert(t = IA.append t (IA.sub (IA.len t-1) 0 t));
  assert(t = IA.append (IA.sub 0 0 t) t);
  assert(t == IA.map (fun x -> x) t);
;;

let test_LPdata () =
  let wc = Unix.gettimeofday () in
  for j = 1 to 400 do
    let test1 = toa [|LP.Con("of",0); of_int 3; of_int 4; LP.Uv (0,0) |] in
    let test2 = toa [|LP.Con("of",0); of_list [cint 3; cint 5] |] in
    for i = 1 to 2000 do
            ignore(LP.equal test1 test2);
            ignore(LP.equal test1 test1);
            let s = Subst.empty 1 in
            assert(s == unify test1 test1 s);
    done;
  done;
  let wc' = Unix.gettimeofday () in
  Printf.eprintf "comparison time: %.3f\n" (wc' -. wc);
;;

let test_whd () =
  let t = LP.(Tup(IA.of_array [| Bin(2, DB 2); Con("a",0); Con("b",0) |])) in
  let t', _ = Red.whd (Subst.empty 0) t in
  Format.eprintf "@[<hv2>whd: @ %a @ ---> %a@]@\n%!"
    (LP.prf_data []) t (LP.prf_data []) t';
  assert(LP.equal t' (LP.Con("a",0)));
  let t = LP.(Tup(IA.of_array [| Bin(2, DB 2); Con("a",0) |])) in
  let t', _ = Red.whd (Subst.empty 0) t in
  Format.eprintf "@[<hv2>whd: @ %a @ ---> %a@]@\n%!"
    (LP.prf_data []) t (LP.prf_data []) t';
  assert(LP.equal t' LP.(Bin(1, Con("a",0))));
  let t = LP.(Tup(IA.of_array [| Bin(2, DB 2); Con("a",0); Con("b",0); Con("c",0) |])) in
  let t', _ = Red.whd (Subst.empty 0) t in
  Format.eprintf "@[<hv2>whd: @ %a @ ---> %a@]@\n%!"
    (LP.prf_data []) t (LP.prf_data []) t';
  assert(LP.equal t' LP.(Tup(IA.of_array [| Con("a",0); Con("c",0) |] )));
  let t = LP.(Tup(IA.of_array [| Bin(2, DB 2); (Bin(1,DB 1)); Con("b",0); Con("c",0) |])) in
  let t', _ = Red.whd (Subst.empty 0) t in
  Format.eprintf "@[<hv2>whd: @ %a @ ---> %a@]@\n%!"
    (LP.prf_data []) t (LP.prf_data []) t';
  assert(LP.equal t' LP.(Con("c",0)));
  ;;

let test_unif () =
  let test b x y = try
    let s = unify x y (Subst.empty 100) in
    Format.eprintf "@[<hv3>unify: %a@ @[<hv0>=== %a@ ---> %a@]@]@\n%!"
      (LP.prf_data []) x (LP.prf_data []) y Subst.prf_subst s;
    let x, y = Red.nf s x, Red.nf s y in
    assert(LP.equal x y)
  with UnifFail s when not b -> 
    Format.eprintf "@[<hv3>unify: %a@ @[<hv0>=/= %a@ ---> %s@]@]@\n%!"
      (LP.prf_data []) x (LP.prf_data []) y (Lazy.force s) in
  test true LP.(Tup(IA.of_array [|Uv(0,0);Con("a1",1)|])) LP.(Con("a1",1));
  test false LP.(Tup(IA.of_array [|Uv(0,0);Con("a0",0)|])) LP.(Con("a0",0));
  test false LP.(Tup(IA.of_array [|Uv(0,0);Con("a1",1);Con("a1",1);|]))
             LP.(Con("a0",0));
  test false LP.(Tup(IA.of_array [|Uv(1,1);DB 1;Con("a1",1);|]))
             LP.(Con("a0",0));
  test false LP.(Tup(IA.of_array [|Uv(1,1);DB 1;DB 1;|]))
             LP.(Con("a0",0));
  test false LP.(Tup(IA.of_array [|Uv(1,1);Uv(1,1);|])) LP.(Con("a0",0));
  test false LP.(Tup(IA.of_array [|Uv(0,0);
                      Tup(IA.of_array [|Con("a1",1);Con("a2",2)|])|]))
             LP.(Con("a0",0));
  test false LP.(Uv(0,0)) LP.(Con("a1",1));
  test false LP.(Con("a",0)) LP.(Con("a",1));
  test true LP.(Con("a1",1)) LP.(Con("a1",1));
  test true LP.(Tup(IA.of_array([|Con("f",0);Con("a1",1);|])))
            LP.(Tup(IA.of_array([|Con("f",0);Con("a1",1);|])));
  test false LP.(Tup(IA.of_array([|Con("f",0);Con("a1",1);|])))
             LP.(Tup(IA.of_array([|Con("f",0);Con("a0",0);|])));
  test false LP.(Tup(IA.of_array([|Con("g",0);Con("a1",1);|])))
             LP.(Tup(IA.of_array([|Con("f",0);Con("a1",1);|])));
  test true LP.(Tup(IA.of_array [|Uv(0,0);Con("a1",1);Con("a2",2)|]))
            LP.(Tup(IA.of_array [|Con("f",0);Con("a2",2);Con("a1",1);|]));
  test false LP.(Tup(IA.of_array [|Uv(0,0);Con("a1",1)|]))
            LP.(Tup(IA.of_array [|Con("a1",1);DB 1;|]));
  test true LP.(Tup(IA.of_array [|Uv(0,0);Con("a1",1);DB 1|]))
            LP.(Tup(IA.of_array [|Con("a1",1);Bin(2,DB 3);|]));
  test true LP.(Bin(6,Tup(IA.of_array [|Uv(0,0);Con("a1",1);DB 1|])))
            LP.(Bin(6,Tup(IA.of_array [|Con("a1",1);Bin(2,DB 3);|])));
;;

let test_coq () =
  Format.eprintf "@[<hv2>embed test:@ %a@]@\n%!"
    (LP.prf_data []) Coq.(embed 
       (Prod("T",Sort true,
         Prod("x",Rel 1,
           App(Const "eq", [|Rel 2; Rel 1; Evar(1,[|Rel 1;Rel 2|]) |])))));
;;

let _ = Printexc.record_backtrace true
let _ =
  if not !Trace.debug then begin
    test_IA ();
    test_LPdata ();
    test_whd ();
    test_unif ();
    test_coq ();
  end;
  Trace.init ~first:0 ~last:max_int false;
  let p = LP.parse_program "
    copy hole hole.
    copy (app A B) (app X Y) :- copy A X, copy B Y.
    copy (lam F) (lam G) :- pi x/ copy x x ==> copy (F x) (G x).
  " in
  let g = LP.parse_goal "
    copy (app (lam w/ lam x/ (app w x)) hole) X.
  " in
  Format.eprintf "@[<hv2>program:@ %a@]@\n%!" LP.prf_program p;
  Format.eprintf "@[<hv2>goal:@ %a@]@\n%!" LP.prf_goal g;
  let s = run p g in
  Format.eprintf "@[<hv2>output:@ %a@]@\n@[<hv2>subst:@ %a@]@\n%!"
    LP.prf_goal (Subst.apply_subst_goal s g) Subst.prf_subst s;
  Format.eprintf "@[<hv2>output:@ %a@]@\n%!"
    LP.prf_goal (LP.map_premise (Red.nf s) g)
