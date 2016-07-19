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

include "pts_dummy/rc_hsat.ma".
(*
(* THE EVALUATION *************************************************************)

(* The arity of a term t in an environment E *)
let rec aa E t on t ≝ match t with
   [ Sort _     ⇒ SORT
   | Rel i      ⇒ nth i … E SORT
   | App M N    ⇒ pred (aa E M)
   | Lambda N M ⇒ let Q ≝ aa E N in ABST Q (aa (Q::E) M)
   | Prod N M   ⇒ aa ((aa E N)::E) M
   | D M        ⇒ aa E M
   ].

interpretation "arity assignment (term)" 'Eval1 t E = (aa E t).

(* The arity of a type context *)
let rec caa E G on G ≝ match G with
   [ nil      ⇒ E
   | cons t F ⇒ let D ≝ caa E F in 〚t〛_[D] :: D
   ].

interpretation "arity assignment (type context)" 'Eval1 G E = (caa E G).

lemma aa_app: ∀M,N,E. 〚App M N〛_[E] = pred (〚M〛_[E]).
// qed.

lemma aa_lambda: ∀M,N,E. 〚Lambda N M〛_[E] = ABST (〚N〛_[E]) (〚M〛_[〚N〛_[E]::E]).
// qed.

lemma aa_prod: ∀M,N,E. 〚Prod N M〛_[E] = 〚M〛_[〚N〛_[E]::E].
// qed.

lemma aa_rel_lt: ∀D,E,i. (S i) ≤ |E| → 〚Rel i〛_[E @ D] = 〚Rel i〛_[E].
#D #E (elim E) -E [1: #i #Hie (elim (not_le_Sn_O i)) #Hi (elim (Hi Hie)) ]
#C #F #IHE #i (elim i) -i // #i #_ #Hie @IHE @le_S_S_to_le @Hie
qed.

lemma aa_rel_ge: ∀D,E,i. (S i) ≰ |E| →
                   〚Rel i〛_[E @ D] = 〚Rel (i-|E|)〛_[D].
#D #E (elim E) -E [ normalize // ]
#C #F #IHE #i (elim i) -i [1: -IHE #Hie (elim Hie) -Hie #Hie (elim (Hie ?)) /2/ ]
normalize #i #_ #Hie @IHE /2/
qed.

(* weakeing and thinning lemma arity assignment *)
(* NOTE: >commutative_plus comes from |a::b| ↦ S |b| rather than |b| + 1 *)
lemma aa_lift: ∀E,Ep,t,Ek.
                 〚lift t (|Ek|) (|Ep|)〛_[Ek @ Ep @ E] = 〚t〛_[Ek @ E].
#E #Ep #t (elim t) -t
   [ #n //
   | #i #Ek @(leb_elim (S i) (|Ek|)) #Hik
     [ >(lift_rel_lt … Hik) >(aa_rel_lt … Hik) >(aa_rel_lt … Hik) //
     | >(lift_rel_ge … Hik) >(aa_rel_ge … Hik) <associative_append
       >(aa_rel_ge …) (>length_append)
       [ >arith2 // @not_lt_to_le /2/ | @(arith3 … Hik) ]
     ]
   | /4/
   | #N #M #IHN #IHM #Ek >lift_lambda >aa_lambda
     >commutative_plus >(IHM (? :: ?)) /3/
   | #N #M #IHN #IHM #Ek >lift_prod >aa_prod
     >commutative_plus >(IHM (? :: ?)) /3/
   | #M #IHM #Ek @IHM
   ]
qed.

(* substitution lemma arity assignment *)
(* NOTE: >commutative_plus comes from |a::b| ↦ S |b| rather than |b| + 1 *)
lemma aa_subst: ∀v,E,t,Ek. 〚t[|Ek|≝v]〛_[Ek @ E] = 〚t〛_[Ek @ 〚v〛_[E]::E].
#v #E #t (elim t) -t
   [ //
   | #i #Ek @(leb_elim (S i) (|Ek|)) #H1ik
     [ >(aa_rel_lt … H1ik) >(subst_rel1 … H1ik) >(aa_rel_lt … H1ik) //
     | @(eqb_elim i (|Ek|)) #H2ik
       [ >(aa_rel_ge … H1ik) >H2ik -H2ik H1ik >subst_rel2
         >(aa_lift ? ? ? ([])) <minus_n_n /2/
       | (lapply (arith4 … H1ik H2ik)) -H1ik H2ik #Hik
         (>(subst_rel3 … Hik)) (>aa_rel_ge) [2: /2/ ] 
          <(associative_append ? ? ([?]) ?) 
           >aa_rel_ge >length_append (>commutative_plus)
           [ <minus_plus // | @not_le_to_not_le_S_S /2/ ]
       ]
     ]
   | //
   | #N #M #IHN #IHM #Ek >subst_lambda > aa_lambda
     >commutative_plus >(IHM (? :: ?)) /3/
   | #N #M #IHN #IHM #Ek >subst_prod > aa_prod
     >commutative_plus >(IHM (? :: ?)) /4/
   | #M #IHM #Ek @IHM
qed.




















(*
(* extensional equality of the interpretations *)
definition eveq: T → T → Prop ≝ λt1,t2. ∀E,K. 〚t1〛_[E, K] ≅ 〚t2〛_[E, K].

interpretation 
   "extensional equality of the type interpretations"
   'napart t1 t2 = (eveq t1 t2).
*)

axiom ev_lift_0_S: ∀t,p,C,E,K. 〚lift t 0 (S p)〛_[C::E, K] ≅ 〚lift t 0 p〛_[E, K].

theorem tj_ev: ∀G,t,u. G ⊢t:u → ∀E,l. l ∈ 〚G〛_[E] → t[l] ∈ 〚u[l]〛_[[], []].
#G #t #u #tjtu (elim tjtu) -G t u tjtu
   [ #i #j #_ #E #l #_ >tsubst_sort >tsubst_sort /2 by SAT0_sort/
   | #G #u #n #tju #IHu #E #l (elim l) -l (normalize)
     [ #_ /2 by SAT1_rel/
     | #hd #tl #_ #H (elim H) -H #Hhd #Htl
       >lift_0 >delift // >lift_0
       
       
       
       (@mem_rceq_trans) [3: @symmetric_rceq @ev_lift_0_S | skip ] 

*)
(* 
theorem tj_sn: ∀G,A,B. G ⊢A:B → SN A.
#G #A #B #tjAB lapply (tj_trc … tjAB (nil ?) (nil ?)) -tjAB (normalize) /3/
qed.
*)

(*
theorem tev_rel_S: ∀i,R,H. 〚Rel (S i)〛_(R::H) = 〚Rel i〛_(H).
// qed.
*)
(*
theorem append_cons: ∀(A:Type[0]). ∀(l1,l2:list A). ∀a.
                     (a :: l1) @ l2 = a :: (l1 @ l2).
// qed.
*)

