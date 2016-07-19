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

inductive t : Type[0] ≝
   leaf: nat → t
 | node: t → t → t.

definition path ≝ list bool.

definition tp ≝ t × path.

let rec setleaf_fun (v:nat) (x:t) (p:path) on p : t × bool ≝
 match p with
 [ nil ⇒
    match x with
    [ leaf _ ⇒ 〈leaf v,true〉
    | node x1 x2 ⇒ 〈node x1 x2,false〉 ]
 | cons b tl ⇒
    match x with
    [ leaf n ⇒ 〈leaf n,false〉
    | node x1 x2 ⇒
       if b then
        let 〈x2',res〉 ≝ setleaf_fun v x2 tl in
         〈node x1 x2', res〉
       else
        let 〈x1',res〉 ≝ setleaf_fun v x1 tl in
         〈node x1' x2, res〉 ]].

let rec admissible (x:t) (p:path) on p : bool ≝
 match p with
 [ nil ⇒ true
 | cons b tl ⇒
    match x with
    [ leaf _ ⇒ false
    | node x1 x2 ⇒
       if b then admissible x2 tl else admissible x1 tl ]].

definition left: ∀A:Type[0]. (bool → tp → A) → tp → A ≝
 λA,k,x.
  let 〈t,p〉 ≝ x in
  let p' ≝ false::p in
   k (admissible t (reverse … p')) 〈t,p'〉.

definition right: ∀A:Type[0]. (bool → tp → A) → tp → A ≝
 λA,k,x.
  let 〈t,p〉 ≝ x in
  let p' ≝ true::p in
   k (admissible t (reverse … p')) 〈t,p'〉.

definition reset: ∀A:Type[0]. (tp → A) → tp → A ≝
 λA,k,x.
  let 〈t,p〉 ≝ x in
   k 〈t,nil …〉.

definition setleaf: ∀A:Type[0]. nat → (bool → tp → A) → tp → A ≝
 λA,v,k,x.
  let 〈t,p〉 ≝ x in
  let 〈t',res〉 ≝ setleaf_fun v t (reverse … p) in
   k res 〈t',p〉.

(*****************************)

let rec update (A:Type[0]) (v:nat) (k: bool → tp → A) (p:path) on p:
 tp → A
≝
 match p with
 [ nil ⇒ setleaf … v (λres. reset … (k res))
 | cons b tl ⇒
    if b then
     right … (λres1.update … v (λres2. k (res1 ∧ res2)) tl)
    else
     left … (λres1. update … v (λres2.k (res1 ∧ res2)) tl) ].

definition example ≝
 node (node (leaf 0) (leaf 1)) (node (leaf 2) (leaf 3)).

lemma test: update ? 5 (λres,x. 〈res,x〉) [false;false] 〈example,nil …〉 = ?.
 normalize //
qed.

lemma setleaf_fun_correct:
 ∀v,p,t.
  admissible t p = false → setleaf_fun v t p = 〈t,false〉.
 #v #p elim p normalize [#t #abs destruct ]
 #hd #tl #IH * normalize // #x1 #x2 cases hd normalize #H >IH //
qed.

lemma rev_append_cons:
 ∀A,x,l1,l2. rev_append A (x::l1) [] @ l2 = rev_append A l1 []@x::l2.
 #A #x #l1 #l2 <(associative_append ?? [?]) <reverse_cons //
qed.

lemma admissible_leaf_cons:
 ∀n,p1,dir,p2. admissible (leaf n) (p1@dir::p2) = false.
 #n #p1 elim p1 //
qed.

lemma admissible_append_true:
 ∀p1,p2,t. admissible t (p1@p2)=true → admissible t p1=true.
 #p1 elim p1 normalize // #hd #tl #IH #p2 * normalize //
 #x1 #x2 cases hd normalize @IH
qed.

theorem update_correct1:
 ∀A,v,p1,p2,k,t.
  admissible t (reverse … p2 @ p1) = false →
   update A v k p1 〈t,p2〉 = k false 〈t,[]〉.
 #A #v #p1 elim p1 normalize
 [ #p2 #k #t #H >setleaf_fun_correct //
 | #hd #tl #IH #p2 #k #t cases hd normalize nodelta
  cases t normalize [1,3:#n|2,4:#x1 #x2] #H >IH // cases (admissible ??) //
qed.

theorem update_correct2:
 ∀A,v,p1,p2,k,t.
  admissible t (reverse … p2 @ p1) = true →
   update A v k p1 〈t,p2〉 = update … v k [] 〈t,reverse … p1 @ p2〉.
#A #v #p1 elim p1 normalize //
#dir #ptl #IH #p2 #k #t cases dir normalize nodelta cases t normalize nodelta
[1,3: #n >admissible_leaf_cons #abs destruct
|*: #x1 #x2 #H >IH
    [2,4: normalize >rev_append_def >associative_append //
    |*: >(rev_append_def … ptl [?]) >associative_append
        >(?:admissible ?? = true) // @(admissible_append_true … ptl) // ]]
qed.
    
theorem final_update_correct:
 ∀v,p1,p2,t.
  let 〈t',res〉 ≝ setleaf_fun v t (reverse … p1 @ p2) in 
  update ? v (λres,x.〈res,x〉) p2 〈t,p1〉 = 〈res,〈t',nil …〉〉.
 #v #p1 #p2 #t @pair_elim #t' #res #EQ inversion (admissible t (reverse … p1 @ p2))
 [ #H >update_correct2 // whd in ⊢ (??%?);
   >(reverse_append ? (reverse ? p2) p1) >reverse_reverse >EQ %
 | #H >update_correct1 // >setleaf_fun_correct in EQ; // ]
qed.