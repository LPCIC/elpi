open Lprun
open Lpdata

let toa x = LP.mkApp(L.of_list x)

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

let cVar,_,_ = C.declare quote (=)
let of_Var s = LP.mkExt (cVar s)

let cSort,_,_ = C.declare (fun x -> quote (sob x)) (=)
let of_Sort s = LP.mkExt (cSort s)

let cName,_,_ = C.declare quote (=)
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
  | Cast(t,ty) -> toa [cast; aux t; aux ty]
  | Prod(n,ty,t) ->  toa [prod; of_Name n; aux ty; LP.mkBin 1 (aux t) ]
  | Lambda(n,ty,t) ->  toa [lam; of_Name n; aux ty; LP.mkBin 1 (aux t) ]
  | App(hd,args) -> aux_app (aux hd) args
  | Const n -> of_Name n
  and aux_app hd args =
     let len_args = Array.length args in
     if len_args = 0 then hd else
     let a = Array.create (len_args + 2) (LP.mkDB 0) in
     a.(0) <- app; a.(1) <- hd;
     for i = 0 to len_args - 1 do a.(i+2) <- aux args.(i); done;
     toa (Array.to_list a)
  in
    aux t

end

let cint,_,_ = C.declare string_of_int (=)
let of_int n = LP.mkExt (cint n)

let clist,_,_ =
  C.declare
    (fun l -> "[" ^ String.concat "; " (List.map C.print l) ^ "]")
    (List.for_all2 C.equal)
let of_list l = LP.mkExt (clist l)

let test_L () =
  let t = L.of_list [ 1; 2; 3; 4; 5 ] in
  assert(t = L.append (L.sub 0 1 t) (L.tl t));
  assert(t = L.append t (L.sub (L.len t-1) 0 t));
  assert(t = L.append (L.sub 0 0 t) t);
(*   assert(t == L.map (fun x -> x) t); *)
;;

let test_LPdata () =
  let wc = Unix.gettimeofday () in
  for j = 1 to 300 do
    let test1 = toa [LP.mkCon "of" 0; of_int 3; of_int 4; LP.mkUv 0 0 ] in
    let test2 = toa [LP.mkCon "of" 0; of_list [cint 3; cint 5] ] in
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
  let test ?(nf=false) a b =
    let t = LP.parse_data a in
    let s = Subst.empty 0 in
    let t', s = if nf then Red.nf t s else Red.whd t s in
    let t'' =  LP.parse_data b in
    Format.eprintf "@[<hv2>whd: @ %a@ ---> %a@]@\n%!"
      (LP.prf_data []) t (LP.prf_data []) t';
    if not (LP.equal t' t'') then begin
      Format.eprintf "@[  =/=  %a@]@\n%!" (LP.prf_data []) t'';
      exit 1;
    end
    in
  test "(x/ y/ x) a b" "a";
  test "(x/ y/ x) a" "y/ a";
  test "(x/ y/ x) a b c" "a c";
  test "(x/ y/ x) (x/ x) b" "x/ x";
  test "(x/ y/ x) (x/ x) b c" "c";
  test "(x/ y/ x) (x/y/ x x y) b c" "y/c c y";
  test ~nf:true "(x/ y/ z/ t/ x r y) (x/y/ x x y) b" "x/y/r r b";
  test "(x/ y/ z/ t/ x r y) (x/y/ x x y) b c c" "r r b";
  test " (x/(y/z/ y) t1 t2) t3" "t1";
  test " (x/(y/z/ [y,z]) c1 c2) X1" "[c1,c2]";
  ;;

let test_unif () =
  let test b x y =
    let x, y = LP.parse_data x, LP.parse_data y in
    try
      let s = unify x y (Subst.empty 100) in
      Format.eprintf "@[<hv3>unify: %a@ @[<hv0>=== %a@ ---> %a@]@]@\n%!"
        (LP.prf_data []) x (LP.prf_data []) y Subst.prf_subst s;
      let x, s = Red.nf x s in let y, s = Red.nf y s in
      if not (LP.equal x y) then begin
        Format.eprintf "@[<hv3>bad unifier: %a@ =/= %a@]@\n%!"
          (LP.prf_data []) x (LP.prf_data []) y;
        exit 1;
      end
    with
    | Lprun.UnifFail s when not b -> 
      Format.eprintf "@[<hv3>unify: %a@ @[<hv0>=/= %a@ ---> %s@]@]@\n%!"
        (LP.prf_data []) x (LP.prf_data []) y (Lazy.force s)
    | Lprun.NOT_A_PU when not b -> 
      Format.eprintf "@[<hv3>unify: %a@ @[<hv0>=/= %a@ ---> %s@]@]@\n%!"
        (LP.prf_data []) x (LP.prf_data []) y "not a PU" in
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
  test true  "a/b/c/f a b c" "f";
  test true  "[]" "nil";
  test true  "[a]" "[a]";
  test true  "[a]" "a :: nil";
  test true  "[a,b,c]" "a :: b :: c :: nil";
  test true  "[a,b,c|X]" "a :: b :: c :: X";
  test false "[]" "[x|B]";
  test true "foo X (X c)" "foo X (@Y L)";
  test true "foo X (X c)" "foo X (?Y L)";
  test false "foo X (X c)" "foo X (#Y L)";
  test true "foo X (X c1 c2) [c1,c2]" "foo X (@Y L) L";
  test true "foo X (X c1 c2) [c2,c1]" "foo X (L Y@) L";
  test false "foo X (X c1 c2) [c1]" "foo X (@Y L) L";
;;

let test_coq () =
  Format.eprintf "@[<hv2>embed test:@ %a@]@\n%!"
    (LP.prf_data []) Coq.(embed 
       (Prod("T",Sort true,
         Prod("x",Rel 1,
           App(Const "eq", [|Rel 2; Rel 1; Evar(1,[|Rel 1;Rel 2|]) |])))));
;;

let test_parse () =
  let test_p s =
    let p = LP.parse_program s in
    Format.eprintf "@[<hv2>program:@ %a@]@\n%!"
      (LP.prf_program ~compact:false) p in
  let test_g s =
    let g = LP.parse_goal s in
    Format.eprintf "@[<hv2>goal:@ %a@]@\n%!" (LP.prf_goal []) g in
  test_p "copy.";
  test_p "copy c d.";
  test_p "copy (foo c) d.";
  test_p "copy (foo c) ((pi x\\ y) = x).";
  test_p "copy (foo c) d :- bar, x :: baz.";
  test_p "copy (foo c) d :- bar, baz.";
  test_p "copy X.";
  test_p "not A :- A, !, false.";
  test_p "copy (lam F) (lam G) :- pi x\\ copy x x => copy (F x) (G x).";
  test_p "copy (lam F) (lam G)/* foo */:- pi x/ copy x x => copy (F x) (G x).";
  test_g "(foo Z :- Z = c) => (foo Y :- Y = a, sigma X/ X = nota) => foo X";
  test_p "foo Y :- $print \"literal\".";
;;

let test_prog p g =
 let width = Format.pp_get_margin Format.err_formatter () in
 for i = 0 to width - 1 do Format.eprintf "-"; done;
 Format.eprintf "@\n%!";
 try
  let p = LP.parse_program p in
  let g = LP.parse_goal g in
  Format.eprintf "@[<hv2>program:@ %a@]@\n%!"
    (LP.prf_program ~compact:false) p;
  let g, s = run p g in
  Format.eprintf
    "@\n@[<hv2>output:@ %a@]@\n@[<hv2>nf out:@ %a@]@\n@[<hv2>subst:@ %a@]@\n%!"
    (LP.prf_goal []) (Subst.apply_subst_goal s g) 
    (LP.prf_goal []) (fst(Red.nf g s))
    Subst.prf_subst s;
 with Stream.Error msg ->
   Format.eprintf "@[Parse error: %s@]@\n%!" msg
;;

let test_copy () =
  test_prog "
    /* clauses for copy */
    copy hole hole.
    copy (app A B) (app X Y) :- copy A X, copy B Y.
    copy (lam F) (lam G) :- pi x/ copy x x => copy (F x) (G x).
    
    /* some test for sigma */
    t1 X :- copy (app (lam w/ lam x/ (app w x)) a) X.
    t2 :- pi x/ sigma Y/ copy x x => copy x Y, copy a a.
    go X W :- (t1 X, t2), W = a."
  "copy a a => go X W"
;;

let test_list () =
  test_prog "
    rev [] [].
    rev [X|Y] T :- rev Y Z, rcons X Z T.
    rcons X [] [X].
    rcons X [Y|Z] [Y|T] :- rcons X Z T. 
  "
  "rev [a,b,c,d] X.";
  test_prog "
    rev A B :- rev-aux A B [].
    rev-aux [] ACC ACC.
    rev-aux [X|Y] T ACC :- rev-aux Y T [X|ACC].
  "
  "rev [a,b,c,d] X.";
;;

let test_aug () =
  test_prog " foo b."
  " (foo Z :- Z = c) => (foo Y :- Y = a, X = nota) => foo X.";
  test_prog " foo b."
  " (foo Z :- Z = c) => (foo Y :- Y = a, sigma X/ X = nota) => foo X."
;;

let test_back () =
  test_prog " foo X :- bar.  foo X :- X = a." "foo a";
  test_prog " go X :- pi w/ sigma A/ A = X w." "go X";
;;

let test_custom () =
  test_prog "foo X Y :- $is_flex X, X = a, Y = X.  foo b c." "foo X Y";
  test_prog "foo X Y :- $is_flex X, X = a, Y = X.  foo b c." "foo b Y";
  test_prog "go :- $print \"test\"." "go";
;;

let test_typeinf () =
  test_prog "
% ML Type inferencer, with abs, app and let.  Chuck liang, 7/95, revised
% from old version of 4/94.  Adopted to Teyjus 7/2000.
% This is a purely declarative L-lambda program.

monotype integer.
monotype (arr A B) :- monotype A, monotype B.

polytype NV (newvar Mgu) (app M N) (all Ty) :-
pi tv/ (sigma Tn/ (sigma Mg/ (sigma Mg2/ (monotype tv => (
  polytype NV Mt1 M Ar1, fill-out Mt1 Ar1 Mt Artype,
  polytype NV Nt1 N T1,    fill-out Nt1 T1 Nt T,
  merge-type T tv Tn,
  typeunify (tv::NV) Tn Artype Mg,
  append-sub Nt Mt MN, merge-sub MN Mg Mg2,
  resolve-sub (tv::NV) (tv::NV) Mg2 (Mgu tv),
  typesub tv (Mgu tv) (Ty tv)))))).

polytype NV (newvar Mgu) (abs M) (all Typ) :-
  pi x/ (pi a/ (sigma A2/ (sigma B/ (sigma Mg/ (sigma Ty/ (monotype a => (
    ((pi Any/ (polytype Any emp x a))
	=> polytype (a::NV) Mg (M x) B), 
    resolve-sub (a::NV) (a::NV) Mg (Mgu a),
    merge-type a B Ty,
    typesub Ty (Mgu a) (Typ a)))))))).

polytype NV M (let R T) C :-
  polytype NV Mt T Ty,
  pi x/ ((pi A/ (polytype A Mt x Ty)) => polytype NV Mr (R x) B),
  append-sub Mr Mt Mrt, resolve-sub NV NV Mrt M,
  typesub B M C.

merge-type (all A) (all B) (all C) :- 
  pi v/ (monotype v => merge-type (A v) (B v) (C v)).
merge-type (all A) B (all C) :- monotype B,
  pi u/ (monotype u => merge-type (A u) B (C u)).
merge-type A (all B) (all C) :- monotype A,
  pi u/ (monotype u => merge-type A (B u) (C u)).
merge-type A B (arr A B) :- monotype A, monotype B.

merge-sub emp L L.
merge-sub (newvar M) (newvar N) (newvar L) :- 
  pi m/ (merge-sub (M m) (N m) (L m)).
merge-sub (newvar M) N (newvar L) :- N = emp,
  pi x/ (copypoly x x => merge-sub (M x) N (L x)).
merge-sub (newvar M) N (newvar L) :- N = (sub A B C),
  pi x/ (copypoly x x => merge-sub (M x) N (L x)).
merge-sub (sub A B C) (newvar N) (newvar L) :- 
  pi x/ (merge-sub (sub A B C) (N x) (L x)).
merge-sub (sub X Y Ss) A (sub X Y B) :- merge-sub Ss A B.

append-sub (newvar M) N (newvar L) :- 
  pi x/ (copypoly x x => append-sub (M x) N (L x)).
append-sub (sub A B C) (newvar N) (newvar L) :- 
  pi z/ (append-sub (sub A B C) (N z) (L z)).
append-sub emp L L.
append-sub (sub X Y Ss) A (sub X Y B) :- append-sub Ss A B.

resolve-for A Vl M N :- M = emp,
  ((pi U/ (vrd A U :- member U Vl)) =>
   ((pi U/ (vrd A U :- rigid U)) => rsub2 Vl A M N)).
resolve-for A Vl M N :- M = (sub X Y Z), 
  ((pi U/ (vrd A U :- rigid U)) =>
   ((pi U/ (vrd A U :- member U Vl)) => rsub2 Vl A M N)).
rsub2 Vl A M (sub A T P) :- collect-for A M AL N, rsub3 (A::Vl) AL T N P.
rsub3 (A::Vl) nil A N N.
rsub3 (A::Vl) (X::nil) X N M :- 
  unify Vl X X U, update-sub N (sub A X U) M.
rsub3 Vl (X::Y::R) Z N M :- 
  unify Vl X Y U, apply_sub X U X2, 
  update-sub N U P, rsub3 Vl (X2::R) Z P M.
collect-for A emp nil emp.
collect-for A (sub A A R) Tr R2 :- collect-for A R Tr R2.
collect-for A (sub A T R) (T::Tr) R2 :- vrd A T, collect-for A R Tr R2.
collect-for A (sub B T R) Tr (sub B T R2) :- vrd A B,
   collect-for A R Tr R2.
collect-for A (sub B T R) Tr (sub B T R2) :- vrd B A,
   collect-for A R Tr R2.

resolve-sub Vs Vl (newvar A) (newvar B) :- 
  pi v/ (append Vs (v::nil) (Vt v),
         append Vl (v::nil) (Vm v),
         resolve-sub (Vt v) (Vm v) (A v) (B v)).
resolve-sub nil Vl A A :- (A = emp).
resolve-sub nil Vl A A :- (A = (sub X Y Z)).
resolve-sub (V::Vs) Vl A C :- (A = emp),
  membrest V Vl Vn,
  resolve-for V Vn A B, resolve-sub Vs Vl B C.
resolve-sub (V::Vs) Vl A C :- (A = (sub X Y Z)),
  membrest V Vl Vn,
  resolve-for V Vn A B, resolve-sub Vs Vl B C.

membrest X (X::Xs) Xs.
membrest X (Y::Xs) (Y::Ys) :- membrest X Xs Ys.

typeunify L (all A) B (newvar Mgu) :- 
  pi t / (monotype t => typeunify (t::L) (A t) B (Mgu t)).
typeunify L A (all B) (newvar Mgu) :- monotype A,
  pi t / (monotype t => typeunify (t::L) A (B t) (Mgu t)).
typeunify L A B Mgu :- monotype A, monotype B,  unify L A B Mgu.

typesub (all A) (newvar U) (all B) :- 
  pi v/ (monotype v => typesub (A v) (U v) (B v)).
typesub (all A) S (all B) :- (S = emp),
  pi x/ (monotype x => (copypoly x x => typesub (A x) S (B x))).
typesub (all A) S (all B) :- (S = (sub X Y Z)),
  pi x/ (monotype x => (copypoly x x => typesub (A x) S (B x))).
typesub A (newvar S) (all B) :- monotype A,
  pi x/ (typesub A (S x) (B x)).
typesub A S B :- monotype A, (S = emp), apply_sub A S B.
typesub A S B :- monotype A, (S = (sub X Y Z)), apply_sub A S B.

apply_sub A (sub X Y Z) B :- copypoly X Y => apply_sub A Z B.
apply_sub A emp B :- copypoly A B.

update-sub emp U emp.
update-sub (sub X Y Z) U (sub X Y2 Z2) :- 
  apply_sub Y U Y2, update-sub Z U Z2.

fill-out N A N A :- monotype A, (N = emp).
fill-out N A N A :- monotype A, (N = (sub X Y Z)).
fill-out (newvar N) (all A) (newvar M) (all B) :- 
  pi u/ (pi v/ (monotype v => fill-out (N u) (A v) (M u) (B v))).
fill-out (newvar N) A (newvar N) (all B) :- monotype A,
  pi u/ (pi v/ (monotype v => fill-out (N u) A (N u) (B v))).
fill-out N (all A) (newvar M) (all A) :- (N = emp),
  pi u/ (pi v/ (monotype v => fill-out N (A v) (M u) (A v))).
fill-out N (all A) (newvar M) (all A) :- (N = (sub X Y Z)),
  pi u/ (pi v/ (monotype v => fill-out N (A v) (M u) (A v))).


% Unification and utilities: ------

copypoly integer integer.
copypoly real real.
copypoly (arr A B) (arr C D) :- copypoly A C, copypoly B D.
rigid integer.
rigid real.
rigid (arr A B).

transform ((diff X X)::S) S Sub Sub :- var X.
transform ((diff integer integer)::S) S Sub Sub.
transform ((diff real real)::S) S Sub Sub.
transform ((diff (arr A B) (arr C D))::S) 
          ((diff A C)::(diff B D)::S) Sub Sub.
transform ((diff X T)::S) S2 Sub (sub X T Sub2) :-
  var X, 
  occur-check X T,
  diff-subst (sub X T emp) S S2,
  sub-subst (sub X T emp) Sub Sub2.

distinct-vars X Y :- var X, var Y, (vrd X Y).
distinct-vars X Y :- var X, var Y, (vrd Y X).

occur-check X integer.
occur-check X real.
occur-check X (arr A B) :- occur-check X A, occur-check X B.
occur-check X Y :- distinct-vars X Y.

unify1 O (V::Vs) A B Sub :-
  (var V, (pi Z/ (vrd V Z :- member Z Vs))) => unify1 O Vs A B Sub.
unify1 O nil A B Sub :- 
  unify0 ((diff A B)::nil) emp Sub1,
  add-trivials O Sub1 Sub.

unify0 nil Sub Sub.
unify0 ((diff A B)::R) Sub Sub2 :-
  var B, rigid A, unify0 ((diff B A)::R) Sub Sub2.
unify0 (D::Ds) Sub Sub3 :-
  transform (D::Ds) S Sub Sub2,
  unify0 S Sub2 Sub3.

unify Vs A B U :- unify1 Vs Vs A B U.


add-trivials nil S S.
add-trivials (V::Vs) S S2 :- in-domain V S, add-trivials Vs S S2.
add-trivials (V::Vs) S (sub V V S2) :- 
  not-indomain V S, add-trivials Vs S S2.

in-domain V (sub V X Y).
in-domain V (sub U X Y) :- in-domain V Y.
not-indomain V emp.
not-indomain V (sub U X Y) :- (vrd V U), not-indomain V Y.
not-indomain V (sub U X Y) :- (vrd U V), not-indomain V Y.


sub_apply A emp A.
sub_apply A (sub V T Ss) B :-
  ((copypoly V T, (pi Y/ (copypoly Y Y :- distinct-vars Y V))) =>
    copypoly A C), sub_apply C Ss B.

diff-subst Sub nil nil.
diff-subst Sub ((diff A B)::R) ((diff C D)::R2) :-
  sub_apply A Sub C, sub_apply B Sub D, 
  diff-subst Sub R R2.

sub-subst Sub emp emp.
sub-subst Sub (sub A B R) (sub C D R2) :-
  sub_apply A Sub C, sub_apply B Sub D,
  sub-subst Sub R R2.

%====

update-sig NV G :-
  ((pi Z/ (copypoly Z Z :- member Z NV)) => 
   ((pi Z/ (rigid Z :- member Z NV)) =>
    ((pi X/ (pi Z/ (occur-check X Z :- member Z NV))) =>
     ((pi Sb/ (pi S/ (pi Z/ (transform ((diff Z Z)::S) S Sb Sb 
			:- member Z NV)))) => G)))).


member X [X|T].
member X [Y|T] :- !, 
member X T.
append [] L L.
append [H|T] L [H|M] :- append T L M.


%=============Examples:============


polytype A emp zero integer.
polytype A emp succ (arr integer integer).
polytype A emp op (all x/ (arr x x)).
polytype A emp op2 (all x/ (all y/ (arr x (arr x x)))).
polytype A emp op3 (all x/ (arr (arr x x) (arr x x))).
polytype A emp op4 (all x/ (all y/ (arr x (arr y y)))).
polytype A emp op5 (all x/ (all y/ (arr (arr x x) (arr y y)))).
polytype A emp op6 (all x/x).  %for separate compilation example

remvac (all x/A) B :- remvac A B.
remvac (all A) (all B) :- 
  pi a/ (monotype a => (appear-in a (A a), remvac (A a) (B a))).
remvac A A :- monotype A.
appear-in A (all B) :- pi x/ (appear-in A (B x)).
appear-in A A :- monotype A.
appear-in A (arr B C) :- appear-in A B.
appear-in A (arr B C) :- appear-in A C.

infer-type N T :- polytype nil M N S, remvac S T.

tryonce X T :- polytype nil M X T, $print T, $print \"\n\", fail.


go :- example X T, tryonce X T.
go :- stop.
stop.
      
example (abs x/ (app op zero)) T.
example (abs f/ (abs x/ (app f x))) T. 
example (abs x/ (abs f/ (app f x))) T.
example (abs f/ (abs g/ (abs x/ (app g (app f x))))) T.
example (abs x/ (abs f/ (app (app f x) (app (app f x) x)))) T.
example (abs f/ (abs x/ (abs y/ (app (app f (app op x)) (app op y))))) T.
example (abs y/ (let (x/ (abs z/x)) (app succ y))) T.
example (let (x/ (app x x)) (abs y/y)) T.
example (let (x/ (let (z/ (app z (app (app x x) (app z z)))) (abs u/u))) (abs y/y)) T. 
example (let (f/ (app (app (abs d1/ (abs (d2 / zero))) (app f zero)) (app f (abs x / x)))) (abs x / x)) T.
example (abs x/ (let (y/x) (app x zero))) T.
example (abs x/ (app op (app op x))) T.
example (abs x/ (let (y/ (app (abs c/c) y)) (app (abs c/c) x))) T.
example (abs x/ (let (u/ (let (v/v) (app succ u))) (app op x))) T.
example (let (u/ (let (v/v) (app op u))) (abs x/x)) T.

% Untypable examples:
example (app (abs x/ (app x x)) (abs x/ (app x x))) T.
example (abs x/ (abs y/ (app (app y x) (app succ y)))) T.
example (abs f/ (let (x/ (app f x)) (app op f))) T.
example (abs x/ (let y/ (app y y)) (app op2 x)) T.
example (abs x/ (let (y/ (app x y)) (app op3 x))) T.
example (abs x/ (let (y/ (app y y)) (app op3 x))) T.
example (abs x/ (let (v/ (app v v)) (abs z/ (app x z)))) T.
example (let (u/ (let (v/v) (app succ u))) (abs x/x)) T.

% some ml equivalents
% fn f => (fn g => (fn x => (g (f x))));
% let val x = (fn y => y) in (let val z = (fn u => u) in (z (x x) (z z)) end) end;
% let val f = (fn x => x) in (((fn d1 => (fn d2 => 0)) (f 0)) (f (fn h => h))) end;"
"go"
;;

let test_refiner () =
  test_prog "

/************************* helpers ************************/

not A :- A, !, false.
not A.

is_flex T :- $is_flex T.

is_same_flex M N :-
  is_flex M, is_flex N, not(dummy1__ = M, dummy2__ = N).

prt S T :- $print S, $print T, $print \"\n\".

%type spy o -> o.
%spy G :- prt \"< \" G, (G, prt \"> \" G ; prt \">fail \" G).

/************************* refiner ************************/

%of M D0_ D1_ D2_ :-  is_flex M, !, prt \"GAME OVER\" M, not true.

of (ginst M T) T (ginst M T) nil :- is_flex M, !.
of (ginst M T) T2 M1 Ex1 :- !, of M T2 M1 Ex1, unify T2 T.

of hole (ginst T set) (ginst M (ginst T set)) [ goal M (ginst T set), goal T set ].

sigma_appl [] [] D0_ D1_ :- !.
sigma_appl [HD|Ss] [decl T S1|Ss1] X T :- HD = S1 X, sigma_appl Ss Ss1 X T.
sigma_appl (append L R) (append L1 R1) X T :- sigma_appl L L1 X T, sigma_appl R R1 X T.

of (lam S F) (prod S2 T) (lam S2 F2) (append Ex1 Ex3) :-
  of S SO S2 Ex1,
  unify SO set,
  pi x/ sigma Ex2/ of x S2 x nil => (
    of (F x) (T x) (F2 x) Ex2,
    sigma_appl Ex2 /*=*/ Ex3 x S2).

of (prod S F) set (prod S2 F2) (append Ex1 Ex3) :-
  of S SO S2 Ex1,
  unify SO set,
  pi x/ sigma Ex2/ of x S2 x nil => (
    of (F x) (T x) (F2 x) Ex2,
    unify (T x) set,
    sigma_appl Ex2 /*=*/ Ex3 x S2).

of (app M1 N1) Z (app M2 N2) (append (append Ex1 Ex2) Ex4) :-
    of M1 TM1 M2 Ex1,
    of N1 TN1 N2 Ex2,
    pi x/ sigma Ex3/
      (of hole (D0_ x) (F x) Ex3,
      unify TM1 (prod TN1 F),
      sigma_appl Ex3 /*=*/ Ex4 x TN1,
      subst F N2 Z).

of (atom ID) T (atom ID) nil :- env ID T.

env zero (atom nat).
env succ (prod (atom nat) (x / (atom nat))).
env plus (prod (atom nat) (x/ prod (atom nat) (y/ (atom nat)))).
env nat set.
env vect (prod (atom nat) (x/ set)).
env vnil (app (atom vect) (atom zero)).
env vcons (prod (atom nat) (n/ prod (app (atom vect) n) (w/ app (atom vect) (app (atom succ) n)))).

of set set set nil.

of (rec Rty N Base Step) Rty2 (rec Rty2 N2 Base2 Step2) (append (append Ex1 Ex2) (append Ex3 Ex4)) :-
  of Rty TRty Rty2 Ex1,
  unify TRty set,
  of N TN N2 Ex2,
  unify TN (atom nat),
  of Base TBase Base2 Ex3,
  unify TBase Rty2,
  of Step TStep Step2 Ex4,
  unify TStep (prod (atom nat) n/ prod Rty2 acc / Rty2).

/* retype */
rof T TY :- of T TY D0_ D1_.

/************************* clean ************************/

% clean L M :- prt \"\" (clean L M), not true.
clean (ginst M T1) R :-
 % prt \"?FLEXIBLE \" M,
 is_flex M, !,
 % prt \"!FLEXIBLE \" M,
 clean T1 T2,
 R = ginst M T2.
clean (ginst M1 D0_) M2 :- !,
 % prt \"!RIGID \" M1,
 clean M1 M2.
clean (app M1 N1) (app M2 N2) :- !, clean M1 M2, clean N1 N2.
clean (lam T1 F1) (lam T2 F2) :- !, clean T1 T2, pi x/ clean (F1 x) (F2 x).
clean (prod T1 F1) (prod T2 F2) :- !, clean T1 T2, pi x/ clean (F1 x) (F2 x).
clean (rec A1 B1 C1 D1) (rec A2 B2 C2 D2) :-
  !, clean A1 A2, clean B1 B2, clean C1 C2, clean D1 D2.
clean T T :- !.

% clean_seq L M :- prt \"\" (clean_seq L M), not true.
clean_seq (decl S1 F1) (decl S2 F2) :- clean S1 S2, pi x/ clean_seq (F1 x) (F2 x).
clean_seq (goal V T1) (goal V T2) :- is_flex V, !, clean T1 T2.

% clean_sigma L D0_ :- prt \"\" (clean_sigma L nil), not true.
clean_sigma [] [].
clean_sigma [X|Xs] [Y|Ys] :- clean_seq X Y, !, clean_sigma Xs Ys.
clean_sigma [D0_|Xs] Ys :- clean_sigma Xs Ys.
clean_sigma (append [] L1) L2 :- clean_sigma L1 L2.
clean_sigma (append [X|Xs] L1) L2 :- clean_sigma (X :: append Xs L1) L2.
clean_sigma (append (append L1 L2) L3) L :- clean_sigma (append L1 (append L2 L3)) L.

/************************* ho ************************/

% ho (lam _ Res) What TYWhat Where

% only mimic in (? ? = T) case
ho (lam LTY (x/T)) (ginst N D0_) LTY T :- is_flex N, !.
ho (lam LTY (x/T)) (app (ginst N D0_) D1_) LTY T :- is_flex N, !.

% proj rigid
ho (lam LTY (x/x)) T LTY T2 :- unify T T2.

% mimic on compound terms
ho (lam LTY (x/ app (L1 x) (R1 x))) T LTY (app L R) :- ho (lam D0_ L1) T LTY L, ho (lam D1_ R1) T LTY R.
ho (lam LTY (x/ rec (A1 x) (B1 x) (C1 x) (D1 x))) T LTY (rec A B C D) :-
 ho (lam D0_ A1) T LTY A, ho (lam D1_ B1) T LTY B, ho (lam D2_ C1) T LTY C, ho (lam D3_ D1) T LTY D.
ho (lam LTY (x/ lam (L1 x) (R1 x))) T LTY (lam L R) :-
 ho (lam D0_ L1) T LTY L, pi x/ ho (lam D1_ (R1 x)) T LTY (R x).
ho (lam LTY (x/ prod (L1 x) (R1 x))) T LTY (prod L R) :-
 ho (lam D0_ L1) T LTY L, pi x/ ho (lam D1_ (R1 x)) T LTY (R x).

% mimic on atomic terms
ho (lam LTY (x/set)) T LTY set.
ho (lam LTY (x/A)) T LTY A :- A = atom D0_.

/************************* copy ************************/

copy (ginst G GT) (ginst G GT1) :- is_flex G, !, copy GT GT1.
copy (ginst G GT) (ginst G1 GT1) :- copy G G1, copy GT GT1.
copy set set.
copy A A :- A = atom D0_.
copy (app A B) (app A1 B1) :- copy A A1, copy B B1.
copy (lam T F) (lam T1 F1) :- copy T T1, pi x/ copy (F x) (F1 x).
copy (prod T F) (prod T1 F1) :- copy T T1, pi x/ copy (F x) (F1 x).

subst Where What Out :- pi x/ copy x What => copy (Where x) Out.

/************************* unify ************************/

%unif A M N :- prt \"\" (unif A M N), not true.

%unif D0_ M D1_ :-  is_flex M, !, prt \"GAME OVER\" M, not true.
%unif D0_ D1_ M :-  is_flex M, !, prt \"GAME OVER\" M, not true.

/* M=M */
unif ff (ginst M TM) (ginst N TN) :- is_same_flex M N, !, unify TM TN.

/* ginst with rigid body */
unif ff (ginst M T) N :- not (is_flex M), !, unify N M.
unif ff N (ginst M T) :- not (is_flex M), !, unify N M.

/* flex=term */
unif ff (ginst M T) N :-
  is_flex M,
  !,
  rof N TN,
  unify TN T,
  M = N.
unif ff N (ginst M T) :-
  is_flex M,
  !,
  rof N TN,
  unify TN T,
  M = N.

/* reflexive closure + heuristic for == */
/*unif ff _ T T :- !.*/
unif ff set set :- !.
unif ff A A :- A = atom D0_, !.

/* contextual closure + heuristic */
unif ff (app H A) (app K B) :- unify H K, unify A B.

/* contextual closure */
unif ff (lam S F) (lam T G) :-
  !,
  unify S T,
  pi x/ of x S x nil => unif ff x x =>
    unify (F x) (G x).

unif ff (prod S F) (prod T G) :-
  !,
  unify S T,
  pi x/ of x S x nil => unif ff x x =>
    unify (F x) (G x).

/* contextual closure + heuristic */
unif ff (rec A1 B1 C1 D1) (rec A2 B2 C2 D2) :-
  unify A1 A2, unify B1 B2, unify C1 C2, unify D1 D2.

/* ho unification */
unif D0_ (app (ginst H TH) M) X :-
  is_flex H, !, rof M TYM, ho H2 M TYM X, unify (ginst H TH) H2.

/* beta */
unif D0_ (app L M) X :-
  L = lam D1_ F,
  !,
  subst F M Y,
  unify Y X.

/* delta */
unif D0_ (atom ID) B :- body ID B.

/* delta */
body plus (lam (atom nat)
             (n/ (rec (prod (atom nat) (x/ (atom nat))) n
                    (lam (atom nat) (x/ x))
                    (lam (atom nat) m/ lam (prod (atom nat) (x/ (atom nat))) acc/
                       lam (atom nat) (n/ app (atom succ) (app acc n)))))) :- !.
/* iota */
unif D0_ (rec D1_ N D2_ D3_) D4_ :- is_flex N, !, fail.
unif D0_ (rec D1_ N B R) X :- N = atom zero, !, unify B X.
unif D0_ (rec T N B R) X :- N = app (atom succ) M, !, unify (app (app R M) (rec T M B R)) X.

/* symmetric */
unif ff A B :- unif tt B A.

unify A B :- unif ff A B.

/* Tactics */

tacsem i     (lam hole (x/ hole)).
tacsem (a M) (app M hole).
tacsem (h N) (var N).
tacsem (r M) M.

/* GUI */

test_unify A B TA2 A2 B2 Sig :-
  prt \"---------> \" (of A TA A1 Ex1),!,
  of A TA A1 Ex1,
  prt \"---------> \" (of B TB B1 Ex2),!,
  of B TB B1 Ex2,
  prt \"========== \" (unify TA TB),!,
  unify TA TB,
  prt \"========== \" (unify A1 B1),!,
  unify A1 B1,
  $print \"cleaning1\n\",!,
  clean TA TA2,
  $print \"cleaning2\n\",
  clean A1 A2,
  $print \"cleaning3\n\",
  clean B1 B2,
  prt \"cleaning4\n\" (append Ex1 Ex2),
  clean_sigma (append Ex1 Ex2) Sig.

  of (var N) T M Sig :- hyp N X, of X T M Sig.
"

 "test_unify (app hole (atom zero)) (app hole (atom zero)) T X Y S"
(*
step_in N (decl TY F) Sig2 :-
  pi x/ sigma Sig/ of x TY x nil => copy x x => unify x x => hyp N x => (
  M is (N + 1),
  prt "" (hyp N TY),
  step_in M (F x) Sig,
  sigma_appl Sig /*=*/ Sig2 x TY).

lread T :- read T, !.
lread T :- print "Not a tactic, retry./n", lread T.

step_in N (goal M MTY) Sig :-
  prt "=========/n" MTY,
  print "/n> ",
  lread T,
  prt "letto " T,
  ((T = undo, !, fail)
  ;(prt "eseguo " T,
    tacsem T P,
    of P TP P1 Sig,
    unify TP MTY,
    print "/nOk/n/n",
    P1 = M)
  ; print "/nWrong! Please retry/n/n", step_in N (goal M MTY) Sig).

step nil :- print "Proof completed./n".
step [G|GS] :-
  (step_in 0 G Sig1,
   clean_sigma (append Sig1 GS) Sig2,
   step Sig2).
  
claim Claim P1 :-
  of Claim T Claim1 Sig1,
  unify T set,
  of hole THole P Sig2,
  unify THole Claim1,
  clean_sigma (append Sig1 Sig2) Sig,
  print "/n",
  step Sig,
  clean P P1. 
  
  ""
  *)
;;

let test_pi () =
        test_prog "foo :- sigma X/ pi x/ pi y/ [x,y] = [x,y]." "foo";
;;


let set_terminal_width () =
  let ic, _ as p = Unix.open_process "tput cols" in
  let w = int_of_string (input_line ic) in
  let _ = Unix.close_process p in
  Format.pp_set_margin Format.err_formatter w;
  Format.pp_set_ellipsis_text Format.err_formatter "...";
  Format.pp_set_max_boxes Format.err_formatter 30;
;;

let _ = Printexc.record_backtrace true
let _ =
  let control = Gc.get () in
  let tweaked_control = { control with
    Gc.minor_heap_size = 33554432; (** 4M *)
    Gc.space_overhead = 120;
  } in
  Gc.set tweaked_control;
  set_terminal_width ();
  let _ = Trace.parse_argv Sys.argv in
  register_custom "print" (fun t s ->
    let t, s = Red.nf t s in
    (match LP.look t with
    | LP.Ext t when isString t -> Format.eprintf "%s%!" (getString t)
    | _ -> Format.eprintf "%a%!" (LP.prf_data []) t);
    s);
  register_custom "is_flex" (fun t s ->
    let t, s = Red.whd t s in
    match LP.look t with
    | LP.Uv _ -> s
    | _ -> raise NoClause);
  test_L ();
  test_LPdata ();
  test_parse ();
  test_whd ();
  test_unif ();
  test_coq ();
  test_copy ();
  test_list ();
  test_aug ();
  test_custom ();
  test_back ();
  test_pi ();
(*   test_refiner (); *)
  test_typeinf ();

