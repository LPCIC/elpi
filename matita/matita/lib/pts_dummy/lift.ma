(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "pts_dummy/terms.ma".

(* to be put elsewhere *)
definition if_then_else ≝ λT:Type[0].λe,t,f.match e return λ_.T with [ true ⇒ t | false ⇒ f].

(* arguments: k is the depth (starts from 0), p is the height (starts from 0) *)
let rec lift t k p ≝
  match t with 
    [ Sort n ⇒ Sort n
    | Rel n ⇒ if_then_else T (leb (S n) k) (Rel n) (Rel (n+p))
    | App m n ⇒ App (lift m k p) (lift n k p)
    | Lambda m n ⇒ Lambda (lift m k p) (lift n (k+1) p)
    | Prod m n ⇒ Prod (lift m k p) (lift n (k+1) p)
    | D n ⇒ D (lift n k p)
    ].

(* 
ndefinition lift ≝ λt.λp.lift_aux t 0 p.

notation "↑ ^ n ( M )" non associative with precedence 40 for @{'Lift O $M}.
notation "↑ _ k ^ n ( M )" non associative with precedence 40 for @{'Lift $n $k $M}.
*)
(* interpretation "Lift" 'Lift n M = (lift M n). *)
interpretation "Lift" 'Lift n k M = (lift M k n). 

(*** properties of lift ***)
(* BEGIN HERE 
lemma lift_0: ∀t:T.∀k. lift t k 0 = t.
#t (elim t) normalize // #n #k cases (leb (S n) k) normalize // 
qed.

(* nlemma lift_0: ∀t:T. lift t 0 = t.
#t; nelim t; nnormalize; //; nqed. *)

lemma lift_sort: ∀i,k,n. lift (Sort i) k n = Sort i.
// qed.

lemma lift_rel: ∀i,n. lift (Rel i) 0 n = Rel (i+n).
// qed.

lemma lift_rel1: ∀i.lift (Rel i) 0 1 = Rel (S i).
#i (change with (lift (Rel i) 0 1 = Rel (1 + i))) //
qed.

lemma lift_rel_lt : ∀n,k,i. i < k → lift (Rel i) k n = Rel i.
#n #k #i #ltik change with 
(if_then_else ? (leb (S i) k) (Rel i) (Rel (i+n)) = Rel i)
>(le_to_leb_true … ltik) //
qed.

lemma lift_rel_ge : ∀n,k,i. k ≤ i → lift (Rel i) k n = Rel (i+n).
#n #k #i #leki change with 
(if_then_else ? (leb (S i) k) (Rel i) (Rel (i+n)) = Rel (i+n))
>lt_to_leb_false // @le_S_S // 
qed.

lemma lift_lift: ∀t.∀m,j.j ≤ m  → ∀n,k. 
  lift (lift t k m) (j+k) n = lift t k (m+n).
#t #i #j #h (elim t) normalize // #n #h #k
@(leb_elim (S n) k) #Hnk normalize
  [>(le_to_leb_true (S n) (j+k) ?) normalize /2/
  |>(lt_to_leb_false (S n+i) (j+k) ?)
     normalize // @le_S_S >(commutative_plus j k)
     @le_plus // @not_lt_to_le /2/
  ]
qed.

lemma lift_lift_up: ∀n,m,t,k,i.
  lift (lift t i m) (m+k+i) n = lift (lift t (k+i) n) i m.
#n #m #N (elim N)
  [1,3,4,5,6: normalize //
  |#p #k #i @(leb_elim i p);
    [#leip >lift_rel_ge // @(leb_elim (k+i) p);
      [#lekip >lift_rel_ge; 
        [>lift_rel_ge // >lift_rel_ge // @(transitive_le … leip) //
        |>associative_plus >commutative_plus @monotonic_le_plus_l // 
        ]
      |#lefalse (cut (p < k+i)) [@not_le_to_lt //] #ltpki
       >lift_rel_lt; [|>associative_plus >commutative_plus @monotonic_lt_plus_r //] 
       >lift_rel_lt // >lift_rel_ge // 
      ]
    |#lefalse (cut (p < i)) [@not_le_to_lt //] #ltpi 
     >lift_rel_lt // >lift_rel_lt; [|@(lt_to_le_to_lt … ltpi) //]
     >lift_rel_lt; [|@(lt_to_le_to_lt … ltpi) //] 
     >lift_rel_lt //
    ]
  ]
qed.

lemma lift_lift_up_sym: ∀n,m,t,k,i.
  lift (lift t i m) (m+i+k) n = lift (lift t (i+k) n) i m.
// qed.

lemma lift_lift_up_01: ∀t,k,p. (lift (lift t k p) 0 1 = lift (lift t 0 1) (k+1) p).
#t #k #p <(lift_lift_up_sym ? ? ? ? 0) //
qed.

lemma lift_lift1: ∀t.∀i,j,k. 
  lift(lift t k j) k i = lift t k (j+i).
/2/ qed.

lemma lift_lift2: ∀t.∀i,j,k. 
  lift (lift t k j) (j+k) i = lift t k (j+i).
/2/ qed.

(*
nlemma lift_lift: ∀t.∀i,j. lift (lift t j) i = lift t (j+i).
nnormalize; //; nqed. *)

(********************* context lifting ********************)

let rec Lift G p ≝ match G with
   [ nil      ⇒ nil …
   | cons t F ⇒ cons … (lift t (|F|) p) (Lift F p)
   ].

interpretation "Lift (context)" 'Lift p G = (Lift G p).

lemma Lift_cons: ∀k,Gk. k = |Gk| → 
                 ∀p,t. Lift (t::Gk) p = lift t k p :: Lift Gk p.
#k #Gk #H >H //
qed.

lemma Lift_length: ∀p,G. |Lift G p| = |G|.
#p #G elim G -G; normalize //
qed. 
*)