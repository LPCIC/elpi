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

include "basics/finset.ma".

record Vector (A:Type[0]) (n:nat): Type[0] ≝ 
{ vec :> list A;
  len: length ? vec = n
}.

record TM (sig:FinSet): Type[1] ≝ 
{ states : FinSet;
  tapes_no: nat;
  trans : states × (option sig) × (Vector (option sig) tapes_no) → 
    states × bool × (Vector (list sig) tapes_no);
  start: states;
  halt : states
}.

definition config ≝ λsig.λM:TM sig.
  states sig M × (list sig) × (Vector (list sig) (tapes_no sig M)).

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
#A #B #l #f elim l //
qed.

definition vec_map ≝ λA,B.λf:A→B.λn.λv:Vector A n.
mk_Vector B n (map ?? f v) 
  (trans_eq … (length_map …) (len A n v)).
  
definition hds ≝ λsig.λM.λc:config sig M. vec_map ?? (option_hd ?) (tapes_no sig M) (\snd c).

definition tls ≝ λsig.λM.λc:config sig M.vec_map ?? (tail ?) (tapes_no sig M) (\snd c).

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

definition step ≝ λsig.λM:TM sig.λc:config sig M.
  match (trans sig M 〈〈\fst (\fst c),option_hd ? (\snd (\fst c))〉,hds sig M c〉) with
  [mk_Prod p l ⇒ 
    let work_tapes ≝ compose_vec ??? (append ?) (tapes_no sig M) l (tls sig M c) in
    match p with 
    [mk_Prod s b ⇒ 
      let old_input ≝ \snd (\fst c) in
      let input ≝ if b then tail ? old_input else  old_input in
      〈〈s,input〉,work_tapes〉]].

definition empty_tapes ≝ λsig.λM:TM sig.
mk_Vector ? (tapes_no sig M) (make_list (list sig) [ ] (tapes_no sig M)) ?.
elim (tapes_no sig M) // normalize //
qed.

definition init ≝ λsig.λM:TM sig.λi:(list sig).
  〈〈start sig M,i〉,empty_tapes sig M〉.

definition stop ≝ λsig.λM:TM sig.λc:config sig M.
  eqb (states sig M) (\fst(\fst c)) (halt sig M).

let rec loop (A:Type[0]) n (f:A→A) p a on n ≝
  match n with 
  [ O ⇒ None ?
  | S m ⇒ if p a then (Some ? a) else loop A m f p (f a)
  ].

definition Compute ≝ λsig.λM:TM sig.λf:(list sig) → (list sig).
∀l.∃i.∃c.((loop ? i (step sig M) (stop sig M) (init sig M l) = Some ? c) ∧
  (hd ? (\snd c) [ ] = f l)).

(* An extended machine *)