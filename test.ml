open Lprun
open Lpdata

let toa x = LP.mkApp(IA.of_array x)

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
let of_Var s = LP.mkExt (cVar s)

let cSort : bool -> C.data =
  C.declare (fun x -> quote (sob x)) (=)
let of_Sort s = LP.mkExt (cSort s)

let cName : string -> C.data = C.declare quote (=)
let of_Name s = LP.mkExt (cName s)



let app  = LP.mkCon "app"  0
let cast = LP.mkCon "cast" 0
let prod = LP.mkCon "prod" 0
let lam  = LP.mkCon "lam"  0
let hole = LP.mkCon "hole" 0

(* module M = Map.Make(struct type t = int let compare = compare end) *)


let embed t (*sigma*) =
(*   let s = ref M.empty in *)
  let rec aux = function
  | Rel n -> LP.mkDB n
  | Var s -> of_Var s
  | Evar (i,ls) -> hole 
  (*aux_app (App [| ginst; M.find i s; aux (sigma i) |]) ls*)
  | Sort s -> of_Sort s
  | Cast(t,ty) -> toa [|cast; aux t; aux ty|]
  | Prod(n,ty,t) ->  toa [|prod; of_Name n; aux ty; LP.mkBin 1 (aux t) |]
  | Lambda(n,ty,t) ->  toa [|lam; of_Name n; aux ty; LP.mkBin 1 (aux t) |]
  | App(hd,args) -> aux_app (aux hd) args
  | Const n -> of_Name n
  and aux_app hd args =
     let len_args = Array.length args in
     if len_args = 0 then hd else
     let a = Array.create (len_args + 2) (LP.mkDB 0) in
     a.(0) <- app; a.(1) <- hd;
     for i = 0 to len_args - 1 do a.(i+2) <- aux args.(i); done;
     toa a
  in
    aux t

end

let cint : int -> C.data = C.declare string_of_int (=)
let of_int n = LP.mkExt (cint n)

let clist : C.data list -> C.data =
  C.declare
    (fun l -> "[" ^ String.concat "; " (List.map C.print l) ^ "]")
    (List.for_all2 C.equal)
let of_list l = LP.mkExt (clist l)

let test_IA () =
  let t = IA.of_array [| 1; 2; 3; 4; 5 |] in
  assert(t = IA.append (IA.sub 0 1 t) (IA.tl t));
  assert(t = IA.append t (IA.sub (IA.len t-1) 0 t));
  assert(t = IA.append (IA.sub 0 0 t) t);
  assert(t == IA.map (fun x -> x) t);
;;

let test_LPdata () =
  let wc = Unix.gettimeofday () in
  for j = 1 to 300 do
    let test1 = toa [|LP.mkCon "of" 0; of_int 3; of_int 4; LP.mkUv 0 0 |] in
    let test2 = toa [|LP.mkCon "of" 0; of_list [cint 3; cint 5] |] in
    for i = 1 to 1000 do
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
  let test a b =
    let t = LP.parse_data a in
    let t', _ = Red.whd (Subst.empty 0) t in
    Format.eprintf "@[<hv2>whd: @ %a @ ---> %a ---> %a@]@\n%!"
      (LP.prf_data []) t
      (LP.prf_data []) t'
      (LP.prf_data []) (Red.nf (Subst.empty 0) t') ;
    assert(LP.equal t' LP.(parse_data b)) in
  test "(x/ y/ x) a b" "a";
  test "(x/ y/ x) a" "y/ a";
  test "(x/ y/ x) a b c" "a c";
  test "(x/ y/ x) (x/ x) b" "x/ x";
  test "(x/ y/ x) (x/ x) b c" "c";
  test "(x/ y/ x) (x/y/ x) b c" "y/c";
  ;;

let test_unif () =
  let test b x y =
    let x, y = LP.parse_data x, LP.parse_data y in
    try
      let s = unify x y (Subst.empty 100) in
      Format.eprintf "@[<hv3>unify: %a@ @[<hv0>=== %a@ ---> %a@]@]@\n%!"
        (LP.prf_data []) x (LP.prf_data []) y Subst.prf_subst s;
      let x, y = Red.nf s x, Red.nf s y in
      if not (LP.equal x y) then begin
        Format.eprintf "@[<hv3>bad unified: %a@ =/= %a@]@\n%!"
          (LP.prf_data []) x (LP.prf_data []) y;
        exit 1;
      end
    with Lprun.UnifFail s when not b -> 
      Format.eprintf "@[<hv3>unify: %a@ @[<hv0>=/= %a@ ---> %s@]@]@\n%!"
        (LP.prf_data []) x (LP.prf_data []) y (Lazy.force s) in
  test true "X a1^1" "a1^1";
  test false "X a" "a";
  test false "X a1^1 a1^1" "b";
  test false "X^1 _1 a1^1" "b";
  test true  "X _1 a1^1" "b";
  test false "X^1 _1 _1" "a";
  test false "X^1 X^1" "a";
  test false "X (f1^1 a2^2)" "b";
  test false "X" "a1^1";
  test false "a" "b1^1";
  test false "a" "b";
  test true  "a1^1" "a1^1";
  test true  "f a1^1" "f a1^1";
  test false "f a1^1" "f b";
  test false "f a" "g a";
  test true  "X a1^1 b2^2" "f b2^2 a1^1";
  test false "X a1^1" "a1^1 _1";
  test true  "X a1^1 _1" "a1^1 x/y/ _3";
  test true  "a/b/c/d/e/f/ X a1^1 f" "a/b/c/d/e/f/ a1^1 x/y/f";
  test true  "a/b/c/f a b c" "f";
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
  Trace.init ~where:("unify",94,99) ~filter_out:["push.*";"epush.*"] false;

  let p = LP.parse_program "
    copy hole hole.
    copy (app A B) (app X Y) :- copy A X, copy B Y.
    copy (lam F) (lam G) :- pi x/ copy x x => copy (F x) (G x).

    t1 X :- copy (app (lam w/ lam x/ (app w x)) a) X.
    t2 :- pi x/ sigma Y/ copy x x => copy x Y, copy a a.
  " in
  let g = LP.parse_goal "copy a a => (t1 X, t2), W = a." in
  Format.eprintf "@[<hv2>program:@ %a@]@\n%!" LP.prf_program p;
  Format.eprintf "@[<hv2>goal:@ %a@]@\n%!" LP.prf_goal g;
  let s = run p g in
  Format.eprintf "@\n@[<hv2>output:@ %a@]@\n@[<hv2>subst:@ %a@]@\n%!"
    LP.prf_goal (Subst.apply_subst_goal s g) Subst.prf_subst s;
  Format.eprintf "@[<hv2>nf output:@ %a@]@\n%!"
    LP.prf_goal (LP.map_premise (Red.nf s) g)
