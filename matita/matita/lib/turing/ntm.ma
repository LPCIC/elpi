(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic   
    ||A||  Library of Mathematics, developed at the Computer Science 
    ||T||  Department of the University of Bologna, Italy.           
    ||I||                                                            
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_____________________________________________________________*)

include "basics/star.ma".
include "turing/turing.ma".

(*
record Vector (A:Type[0]) (n:nat): Type[0] ≝ 
{ vec :> list A;
  len: length ? vec = n
}.

record tape (sig:FinSet): Type[0] ≝ 
{ left : list sig;
  right: list sig
}.

inductive move : Type[0] ≝
| L : move 
| R : move
| N : move
. 
*)

record NTM (sig:FinSet): Type[1] ≝ 
{ states : FinSet;
  tapes_no: nat; (* additional working tapes *)
  trans : list ((states × (Vector (option sig) (S tapes_no))) ×
    (states  × (Vector (sig × move) (S tapes_no))));
  output: list sig;
  start: states;
  halt : states → bool;
  accept : states → bool
}.

record config (sig:FinSet) (M:NTM sig): Type[0] ≝
{ state : states sig M;
  tapes : Vector (tape sig) (S (tapes_no sig M))
}.

(*
definition option_hd ≝ λA.λl:list A.
  match l with
  [nil ⇒ None ?
  |cons a _ ⇒ Some ? a
  ].

lemma length_tail: ∀A,l. length ? (tail A l) = pred (length ? l).
#A #l elim l // 
qed.

definition vec_tail ≝ λA.λn.λv:Vector A n.
mk_Vector A (pred n) (tail A v) ?.
>length_tail >(len A n v) //
qed.

definition vec_cons ≝ λA.λa.λn.λv:Vector A n.
mk_Vector A (S n) (cons A a v) ?.
normalize >(len A n v) //
qed.

lemma length_map: ∀A,B,l.∀f:A→B. length ? (map ?? f l) = length ? l.
#A #B #l #f elim l // #a #tl #Hind normalize //
qed.

definition vec_map ≝ λA,B.λf:A→B.λn.λv:Vector A n.
mk_Vector B n (map ?? f v) 
  (trans_eq … (length_map …) (len A n v)). 
  
definition tape_move ≝ λsig.λt: tape sig.λm:sig × move.
  match \snd m with
  [ R ⇒ mk_tape sig ((\fst m)::(left ? t)) (tail ? (right ? t))
  | L ⇒ mk_tape sig (tail ? (left ? t)) ((\fst m)::(right ? t))
  ].
*)

(*  
definition hds ≝ λsig.λM.λc:config sig M. vec_map ?? (option_hd ?) (tapes_no sig M) (\snd c).

definition tls ≝ λsig.λM.λc:config sig M.vec_map ?? (tail ?) (tapes_no sig M) (\snd c).
*)
(*
let rec compose A B C (f:A→B→C) l1 l2 on l1 ≝
   match l1 with
   [ nil ⇒ nil C
   | cons a tlA ⇒ 
     match l2 with
     [nil ⇒ nil C
     |cons b tlB ⇒ (f a b)::compose A B C f tlA tlB
     ]
   ].

lemma length_compose: ∀A,B,C.∀f:A→B→C.∀l1,l2.
length C (compose  A B C f l1 l2) = 
  min (length A l1) (length B l2).
#A #B #C #f #l1 elim l1 // #a #tlA #Hind #l2 cases l2 //
#b #tlB lapply (Hind tlB) normalize 
cases (true_or_false (leb (length A tlA) (length B tlB))) #H >H
normalize //
qed.

definition compose_vec ≝ λA,B,C.λf:A→B→C.λn.λvA:Vector A n.λvB:Vector B n.
mk_Vector C n (compose A B C f vA vB) ?.
>length_compose >(len A n vA) >(len B n vB) normalize 
>(le_to_leb_true … (le_n n)) //
qed.
*)

definition current_chars ≝ λsig.λM:NTM sig.λc:config sig M.
  vec_map ?? (λt.option_hd ? (right ? t)) (S (tapes_no sig M)) (tapes ?? c).

let rec mem A (a:A) (l:list A) on l ≝
  match l with
  [ nil ⇒ False
  | cons hd tl ⇒ a=hd ∨ mem A a tl
  ]. 
(* this no longer works: TODO 
definition reach ≝ λsig.λM:NTM sig.λc,c1:config sig M.
  ∃q,l,q1,mvs. 
    state ?? c = q ∧ 
    halt ?? q = false ∧
    current_chars ?? c = l ∧
    mem ? 〈〈q,l〉,〈q1,mvs〉〉 (trans ? M)  ∧ 
    state ?? c1 = q1 ∧
    tapes ?? c1 = (compose_vec ??? (tape_move sig) ? (tapes ?? c) mvs).
*)
(*
definition empty_tapes ≝ λsig.λn.
mk_Vector ? n (make_list (tape sig) (mk_tape sig [] []) n) ?.
elim n // normalize //
qed.
*)
(* this no longer works: TODO
definition init ≝ λsig.λM:NTM sig.λi:(list sig).
  mk_config ??
    (start sig M)
    (vec_cons ? (mk_tape sig [] i) ? (empty_tapes sig (tapes_no sig M))).

definition accepted ≝ λsig.λM:NTM sig.λw:(list sig).
∃c. star ? (reach sig M) (init sig M w) c ∧
  accept ?? (state ?? c) = true.
*)