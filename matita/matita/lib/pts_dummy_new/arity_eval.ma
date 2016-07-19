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

include "pts_dummy/arity.ma".
(*
(* ARITY ASSIGNMENT ***********************************************************)

(* the arity type *************************************************************)

(* arity type assigned to the term t in the environment E *)
let rec ata K t on t ≝  match t with
   [ Sort _     ⇒ TOP
   | Rel i      ⇒ nth i … K TOP
   | App M N    ⇒ pred (ata K M) 
   | Lambda N M ⇒ let C ≝ ata K N in FUN C (ata (C::K) M)
   | Prod _ _   ⇒ TOP
   | D M        ⇒ TOP (* ??? not so sure yet *)
   ].

interpretation "arity type assignment" 'IInt1 t K = (ata K t).

lemma ata_app: ∀M,N,K. 〚App M N〛_[K] = pred (〚M〛_[K]).
// qed.

lemma ata_lambda: ∀M,N,K. 〚Lambda N M〛_[K] = FUN (〚N〛_[K]) (〚M〛_[〚N〛_[K]::K]).
// qed.

lemma ata_rel_lt: ∀H,K,i. (S i) ≤ |K| → 〚Rel i〛_[K @ H] = 〚Rel i〛_[K].
#H #K elim K -K [1: #i #Hie elim (not_le_Sn_O i) #Hi elim (Hi Hie) ]
#A #K #IHK #i elim i -i // #i #_ #Hie @IHK @le_S_S_to_le @Hie
qed.

lemma ata_rel_ge: ∀H,K,i. (S i) ≰ |K| →
                  〚Rel i〛_[K @ H] = 〚Rel (i-|K|)〛_[H].
#H #K elim K -K [ normalize // ]
#A #K #IHK #i elim i -i [1: -IHK #Hie elim Hie -Hie #Hie; elim (Hie ?) /2/ ]
normalize #i #_ #Hie @IHK /2/
qed.

(* weakeing and thinning lemma for the arity type assignment *)
(* NOTE: >commutative_plus comes from |a::b| ↦ S |b| rather than |b| + 1 *)
lemma ata_lift: ∀p,K,Kp. p = |Kp| → ∀t,k,Kk. k = |Kk| →
                〚lift t k p〛_[Kk @ Kp @ K] = 〚t〛_[Kk @ K].
#p #K #Kp #HKp #t elim t -t //
   [ #i #k #Kk #HKk @(leb_elim (S i) k) #Hik
     [ >(lift_rel_lt … Hik) >HKk in Hik #Hik
       >(ata_rel_lt … Hik) >(ata_rel_lt … Hik) //
     | >(lift_rel_ge … Hik) >HKk in Hik #Hik
       >(ata_rel_ge … Hik) <associative_append
       >(ata_rel_ge …) >length_append >HKp;
       [ >arith2 // @not_lt_to_le /2/ | @(arith3 … Hik) ]
     ]
   | #M #N #IHM #_ #k #Kk #HKk >lift_app >ata_app /3/
   | #N #M #IHN #IHM #k #Kk #HKk >lift_lambda >ata_lambda
     >IHN // >(IHM … (? :: ?)) // >commutative_plus /2/ 
   ]
qed.

(* substitution lemma for the arity type assignment *)
(* NOTE: >commutative_plus comes from |a::b| ↦ S |b| rather than |b| + 1 *)
lemma ata_subst: ∀v,K,t,k,Kk. k = |Kk| → 
                 〚t[k≝v]〛_[Kk @ K] = 〚t〛_[Kk @ 〚v〛_[K]::K].
#v #K #t elim t -t //
   [ #i #k #Kk #HKk @(leb_elim (S i) k) #H1ik
     [ >(subst_rel1 … H1ik) >HKk in H1ik #H1ik
       >(ata_rel_lt … H1ik) >(ata_rel_lt … H1ik) //
     | @(eqb_elim i k) #H2ik
       [ >H2ik in H1ik -H2ik i #H1ik >subst_rel2 >HKk in H1ik #H1ik
         >(ata_rel_ge … H1ik) <minus_n_n >(ata_lift ? ? ? ? ? ? ([])) //
       | lapply (arith4 … H1ik H2ik) -H1ik H2ik #Hik >(subst_rel3 … Hik)
          >ata_rel_ge; [2: /2/ ] <(associative_append ? ? ([?]) ?)
           >ata_rel_ge >length_append >commutative_plus;
           [ <minus_plus // | <HKk -HKk Kk @not_le_to_not_le_S_S /3/ ]
       ]
     ]
   | #M #N #IHM #_ #k #Kk #HKk >subst_app >ata_app /3/
   | #N #M #IHN #IHM #k #Kk #HKk >subst_lambda > ata_lambda
     >IHN // >commutative_plus >(IHM … (? :: ?)) /2/
   ]
qed.

(* the arity ******************************************************************)

(* arity assigned to the term t in the environments E and K *)
let rec aa K E t on t ≝ match t with
   [ Sort _     ⇒ sort
   | Rel i      ⇒ nth i … E sort
   | App M N    ⇒ aapp (〚N〛_[K]) (aa K E M) (aa K E N)
   | Lambda N M ⇒ aabst (λc. aa (〚N〛_[K]::K) (c :: E) M)
   | Prod N M   ⇒ aabst (λc. aa (〚N〛_[K]::K) (c :: E) M)
   | D M        ⇒ sort (* ??? not so sure yet *)
   ].

interpretation "arity assignment" 'IInt2 t E K = (aa K E t).

lemma aa_app: ∀M,N,E,K. 〚App M N〛_[E,K] = aapp (〚N〛_[K]) (〚M〛_[E,K]) (〚N〛_[E,K]).
// qed.

lemma aa_lambda: ∀N,M,E,K. 〚Lambda N M〛_[E,K] = aabst (λc. 〚M〛_[c :: E, 〚N〛_[K]::K]).
// qed.

lemma aa_prod: ∀N,M,E,K. 〚Prod N M〛_[E,K] = aabst (λc. 〚M〛_[c :: E, 〚N〛_[K]::K]).
// qed.

lemma aa_rel_lt: ∀K2,K1,D,E,i. (S i) ≤ |E| →
                 〚Rel i〛_[E @ D, K1] = 〚Rel i〛_[E, K2].
#K1 #K1 #D #E elim E -E [1: #i #Hie elim (not_le_Sn_O i) #Hi elim (Hi Hie) ]
#C #E #IHE #i elim i -i // #i #_ #Hie @IHE @le_S_S_to_le @Hie
qed.

lemma aa_rel_lt_id: ∀K,D,E,i. (S i) ≤ |E| →
                    〚Rel i〛_[E @ D, K] = 〚Rel i〛_[E, K].
#K @(aa_rel_lt K) qed.

lemma aa_rel_ge: ∀K2,K1,D,E,i. (S i) ≰ |E| →
                 〚Rel i〛_[E @ D, K1] = 〚Rel (i-|E|)〛_[D, K2].
#K2 #K1 #D #E elim E -E [ normalize // ]
#C #E #IHE #i elim i -i [1: -IHE #Hie elim Hie -Hie #Hie elim (Hie ?) /2/ ]
normalize #i #_ #Hie @IHE /2/
qed.

lemma aa_rel_ge_id: ∀K,D,E,i. (S i) ≰ |E| →
                    〚Rel i〛_[E @ D, K] = 〚Rel (i-|E|)〛_[D, K].
#K @(aa_rel_ge K) qed.

(* weakeing and thinning lemma for the arity assignment *)
(* NOTE: >commutative_plus comes from |a::b| ↦ S |b| rather than |b| + 1 *)
lemma aa_lift: ∀K,E1,E2. E1 ≅ E2 → ∀p,Kp,Ep. p=|Kp| → p = |Ep| →
               ∀t,k,Kk,E1k,E2k. k = |Kk| → k = |E1k| → E1k ≅ E2k →
               〚lift t k p〛_[E1k @ Ep @ E1, Kk @ Kp @ K] ≅ 〚t〛_[E2k @ E2, Kk @ K].
#K #E1 #E2 #HE #p #Kp #Ep #HKp #HEp #t elim t -t /2 by invariant_sort/
   [ #i #k #Kk #E1k #E2k #HKk #HE1k #HEk @(leb_elim (S i) k) #Hik
     [ >(lift_rel_lt … Hik) >HE1k in Hik #Hik >(aa_rel_lt_id … Hik)
       >(all2_length … HEk) in Hik #Hik >(aa_rel_lt_id … Hik) /2 by nth_sort_comp/
     | >(lift_rel_ge … Hik) >HE1k in Hik #Hik <(associative_append … E1k)
       >(aa_rel_ge_id …) >length_append >HEp; [2: @(arith3 … Hik) ]
       >(all2_length … HEk) in Hik #Hik >(aa_rel_ge_id … Hik) >arith2;
       [ /2 by nth_sort_comp/ | @not_lt_to_le /2/ ]
     ]
   | #M #N #IHM #IHN #k #Kk #E1k #E2k #HKk #HE1k #HEk >lift_app >aa_app
     >ata_lift /3/
   | #N #M #_ #IHM #k #Kk #E1k #E2k #HKk #HE1k #HEk >lift_lambda >aa_lambda
     @aabst_comp #a1 #a2 #Ha >ata_lift // >commutative_plus
     @(IHM ? (?::?) (?::?) (?::?)); [ >HKk | >HE1k ] /2/
   | #N #M #_ #IHM #k #Kk #E1k #E2k #HKk #HE1k #HEk >lift_prod >aa_prod
     @aabst_comp #a1 #a2 #Ha >ata_lift // >commutative_plus
     @(IHM ? (?::?) (?::?) (?::?)); [ >HKk | >HE1k ] /2/
   ]
qed.

lemma aa_comp: ∀E1,E2. E1 ≅ E2 → ∀t,K. 〚t〛_[E1, K] ≅ 〚t〛_[E2, K].
#E1 #E2 #HE #t #K <(lift_0 t 0) in ⊢ (? % ?)
@(aa_lift … ([]) ([]) … ([]) ([]) ([])) //
qed.

(* the assigned arity is invariant *)
lemma aa_invariant: ∀t,E,K. !E → !〚t〛_[E, K].
/2/ qed.

(* substitution lemma for the arity assignment *)
(* NOTE: >commutative_plus comes from |a::b| ↦ S |b| rather than |b| + 1 *)
lemma aa_subst: ∀K,E1,E2. E1 ≅ E2 →
                ∀v,t,k,Kk,E1k,E2k. k = |Kk| → k = |E1k| → E1k ≅ E2k →
                〚t[k≝v]〛_[E1k@E1, Kk@K] ≅ 〚t〛_[E2k@〚v〛_[E2,K]::E2, Kk@〚v〛_[K]::K].
#K #E1 #E2 #HE #v #t elim t -t /2 by invariant_sort/
   [ #i #k #Kk #E1k #E2k #HKk #HE1k #HEk @(leb_elim (S i) k) #H1ik
     [ >(subst_rel1 … H1ik) >HE1k in H1ik #H1ik >(aa_rel_lt_id … H1ik)
       >(all2_length … HEk) in H1ik #H1ik >(aa_rel_lt_id … H1ik) /2/
     | @(eqb_elim i k) #H2ik
       [ >H2ik in H1ik -H2ik i #H1ik >subst_rel2 >HE1k in H1ik #H1ik
         >(all2_length … HEk) in H1ik #H1ik >(aa_rel_ge_id … H1ik) <minus_n_n
         >HE1k in HKk #HKk -HE1k k  >(all2_length … HEk) in HKk #HKk
         @(aa_lift … ([]) ([]) ([])) /3/
       | lapply (arith4 … H1ik H2ik) -H1ik H2ik #Hik
         >(subst_rel3 … Hik) >aa_rel_ge_id; [2: /2/ ]
         <(associative_append ? ? ([?]) ?) in ⊢ (? ? (? ? % ?))
         >HE1k in Hik #Hik >(aa_rel_ge (Kk@K))
         >length_append >commutative_plus <(all2_length … HEk);
         [ <minus_plus /2/ | @not_le_to_not_le_S_S /3/ ]
       ]
     ]
   | #M #N #IHM #IHN #k #Kk #E1k #E2k #HKk #HE1k #HEk >subst_app >aa_app
     >ata_subst /3/
   | #N #M #_ #IHM #k #Kk #E1k #E2k #HKk #HE1k #HEk >subst_lambda >aa_lambda
     @aabst_comp #a1 #a2 #Ha >ata_subst // >commutative_plus
     @(IHM ? (?::?) (?::?) (?::?)); [ >HKk | >HE1k ] /2/
   | #N #M #_ #IHM #k #Kk #E1k #E2k #HKk #HE1k #HEk >subst_prod >aa_prod
     @aabst_comp #a1 #a2 #Ha >ata_subst // >commutative_plus
     @(IHM ? (?::?) (?::?) (?::?)); [ >HKk | >HE1k ] /2/
   ]
qed.

(* the assigned arity is constant *)
lemma aa_isc: ∀t,E,K. !E → all2 … isc E K → isc (〚t〛_[E,K]) (〚t〛_[K]).
#t elim t -t /2 by isc_sort/
   [ #i #E #K #HE #H @(all2_nth … isc) //
   | /3/
   | #N #M #IHN #IHM #E #K #HE #H >aa_lambda >ata_lambda 



(*
const ? (〚v〛_[E1,K] (〚v〛_[K])) ≅ 〚v〛_[E1,K].

theorem aa_beta: ∀K,E1,E2. E1 ≅ E2 → ∀w,t,v. 〚v〛_[K] = 〚w〛_[K] →
                 〚App (Lambda w t) v〛_[E1,K] ≅ 〚t[0≝v]〛_[E2,K].
#K #E1 #E2 #HE #w #t #v #H > aa_app >aa_lambda
@transitive_aeq; [3: @symmetric_aeq @(aa_subst … E1 … ([]) ([]) ([])) /2/ | skip ]
>H @aa_comp -H v; #C whd in ⊢ (? ? % ?)
*)

(*
axiom cons_comp: ∀a1,a2. a1 ≅ a2 → ∀E1,E2. E1 ≅ E2 → a1 :: E1 ≅ a2 :: E2.

axiom pippo: ∀A:Type[0]. ∀a,b,c. (a::b) @ c = a :: b @ c.
@A qed.
*)
*)
