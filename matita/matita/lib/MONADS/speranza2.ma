(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "basics/types.ma".
include "arithmetics/nat.ma".
include "basics/lists/list.ma".

inductive T : Type[0] ≝
   leaf: nat → T
 | node: T → T → T.

definition path ≝ list bool.

definition option_map: ∀A,B:Type[0]. (A → option B) → option A → option B ≝
 λA,B,f,x. match x with [ None ⇒ None … | Some v ⇒ f v ].

definition left: ∀A:Type[0]. (T → option T) → (T → option A) → T → option A ≝
 λA,kl,k,t.
  match t with
  [ leaf _ ⇒ None ?
  | node l r ⇒ option_map … (λl'. k (node l' r)) (kl l) ].

definition right: ∀A:Type[0]. (T → option T) → (T → option A) → T → option A ≝
 λA,kr,k,t.
  match t with
  [ leaf _ ⇒ None ?
  | node l r ⇒ option_map … (λr'. k (node l r')) (kr r) ].

definition setleaf: ∀A:Type[0]. (nat → option nat) → (T → option A) → T → option A ≝
 λA,kv,k,t.
  match t with
  [ leaf n ⇒ option_map … (λn'. k (leaf n')) (kv n)
  | node l r ⇒ None ? ].

definition stop: T → option T ≝
 λt. Some … t.

(*****************************)

let rec setleaf_fun (v:nat) (x:T) (p:path) on p : option T ≝
 match p with
 [ nil ⇒
    match x with
    [ leaf _ ⇒ Some … (leaf v)
    | node x1 x2 ⇒ None ? ]
 | cons b tl ⇒
    match x with
    [ leaf n ⇒ None …
    | node x1 x2 ⇒
       if b then
        option_map … (λx2'. Some … (node x1 x2')) (setleaf_fun v x2 tl)
       else
        option_map … (λx1'. Some … (node x1' x2)) (setleaf_fun v x1 tl) ]].

let rec update (A:Type[0]) (v:nat) (k: T → option A) (p:path) on p: T → option A ≝
 match p with
 [ nil ⇒ setleaf … (λ_. Some … v) k
 | cons b tl ⇒
    if b then right … (update T v stop tl) k else left … (update T v stop tl) k ].

let rec add_fun (t1:T) (t2:T) on t2 : option T ≝
 match t1 with
 [ leaf m ⇒ match t2 with [ leaf n ⇒ Some … (leaf (m+n)) | _ ⇒ None ? ]
 | node l1 r1 ⇒
    match t2 with
    [ node l2 r2 ⇒
       option_map … (λl'.
        option_map … (λr'. Some … (node l' r')) (add_fun r1 r2)) (add_fun l1 l2)
    | _ ⇒ None … ]].

let rec add (A:Type[0]) (k: T → option A) (t1:T) on t1 : T → option A ≝
 match t1 with
 [ leaf n ⇒ setleaf … (λm.Some … (n+m)) k
 | node l r ⇒
    left … (add … stop l) (right … (add … stop r) k) ].

definition example ≝
 node (node (leaf 0) (leaf 1)) (node (leaf 2) (leaf 3)).

lemma test: add … stop example example = ?.
 normalize //
qed.

lemma test1: update ? 5 stop [false;false] example = ?.
 normalize //
qed.

theorem update_correct:
 ∀v,p,t. setleaf_fun v t p =  update ? v stop p t.
#v #p elim p normalize [* normalize // ]
#hd #tl #IH * normalize
 [ cases hd normalize //
 | cases hd normalize #l #r >IH // ]
qed.

theorem add_correct: ∀t1,t2. add_fun t1 t2 = add … stop t1 t2.
 #t1 elim t1 normalize
  [ #n * normalize //
  | #l1 #r1 #IHl #IHr * normalize // #l2 #r2 >IHl >IHr // ]
qed.