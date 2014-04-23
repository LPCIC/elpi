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
  let test ?(nf=false) a b =
    let t = LP.parse_data a in
    let s = Subst.empty 0 in
    let t' = if nf then Red.nf s t else fst(Red.whd s t) in
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
  test true  "a/b/c/f a b c" "f";
  test true  "[]" "nil";
  test true  "[a]" "[a]";
  test true  "[a]" "a :: nil";
  test true  "[a,b,c]" "a :: b :: c :: nil";
  test true  "[a,b,c|X]" "a :: b :: c :: X";
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
    Format.eprintf "@[<hv2>program:@ %a@]@\n%!" LP.prf_program p in
  let test_g s =
    let hv, g, s = prepare_initial_goal (LP.parse_goal s) in
    Format.eprintf "@[<hv2>goal:@ %a@]@\n%!"
      (LP.prf_goal (ctx_of_hv hv)) (Subst.apply_subst_goal s g) in
  test_p "copy (lam F) (lam G) :- pi x\\ copy x x => copy (F x) (G x).";
  test_g " (foo Z :- Z = c) => (foo Y :- Y = a, sigma X/ X = nota) => foo X";
;;

let test_prog p g =
 let width = Format.pp_get_margin Format.err_formatter () in
 for i = 0 to width - 1 do Format.eprintf "-"; done;
 Format.eprintf "@\n%!";
 try
  let p = LP.parse_program p in
  let g = LP.parse_goal g in
  Format.eprintf "@[<hv2>program:@ %a@]@\n%!" LP.prf_program p;
  let g, s = run p g in
  Format.eprintf
    "@\n@[<hv2>output:@ %a@]@\n@[<hv2>nf out:@ %a@]@\n@[<hv2>subst:@ %a@]@\n%!"
    (LP.prf_goal []) (Subst.apply_subst_goal s g) 
    (LP.prf_goal []) (LP.map_premise (Red.nf s) g)
    Subst.prf_subst s;
 with Stream.Error msg ->
   Format.eprintf "@[Parse error: %s@]@\n%!" msg
;;

let test_copy () =
  test_prog "
    copy hole hole.
    copy (app A B) (app X Y) :- copy A X, copy B Y.
    copy (lam F) (lam G) :- pi x/ copy x x => copy (F x) (G x).
    
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
  test_prog " foo X :- bar.  foo X :- X = a."
  "foo a";
;;

let test_custom () =
  register_custom "is_flex" (fun t s _ _ ->
    let t, s = Red.whd s t in
    match LP.look t with
    | LP.Uv _ -> s
    | _ -> raise NoClause);
  test_prog "foo X Y :- $is_flex X, X = a, Y = X.  foo b c." "foo X Y";
  test_prog "foo X Y :- $is_flex X, X = a, Y = X.  foo b c." "foo b Y";
;;

let test_typeinf () =
  register_custom "print" (fun t s _ _ ->
    let t = Red.nf s t in
    Format.eprintf "%a@\n%!" (LP.prf_data []) t;
    s);
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

tryonce X T :- polytype nil M X T, $print X, $print T, fail.


go :- example X T, tryonce X T.
go :- stop.
stop :- $print the-end.
      
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
  set_terminal_width ();
  test_IA ();
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
(*    Trace.init ~where:("run",1,1000) ~filter_out:["rdx";"push.*";"epush.*";"unif";"bind";"t$";"vj$";"rule";"whd";"hv";"premise";"sub"] true; *)
  test_typeinf ();

