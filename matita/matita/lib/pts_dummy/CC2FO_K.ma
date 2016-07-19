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

include "pts_dummy/degree.ma".
(*
(* TO BE PUT ELSEWERE *)
lemma cons_append_assoc: ∀A,a. ∀l1,l2:list A. (a::l1) @ l2 = a :: (l1 @ l2).
// qed.

(* λPω → λω MAPPING ***********************************************************)
(* The idea [1] is to map a λPω-type T to a λω-type J(T) representing the
 * structure of the saturated subset (s.s.) of the λPω-terms for the type T.
 * To this aim, we encode:
 * 1) SAT (the collection of the (dependent) families of s.s.) as □
 * 2) Sat (the union of the families in SAT) as ∗
      [ sat (the family of s.s.) does not need to be distinguisched from Sat ]
 * 3) sn (the full saturated subset) as a constant 0 of type ∗
 * [1] H. H.P. Barendregt (1993) Lambda Calculi with Types,
 *     Osborne Handbooks of Logic in Computer Science (2) pp. 117-309
 *)

(* The K interpretation of a term *********************************************)

(* the interpretation in the λPω-context G of t (should be λPω-kind or □)
 * as a member of SAT
 *)
let rec Ki G t on t ≝ match t with
[ Sort _     ⇒ Sort 0
| Prod n m   ⇒ 
    let im ≝ Ki (n::G) m in 
    if_then_else ? (eqb (║n║_[║G║]) 3) (Prod (Ki G n) im) im[0≝Sort 0]
(* this is correct if we want dummy kinds *)
| D _        ⇒ Sort 0
(* this is for the substitution lemma *)
| Rel i      ⇒ Rel i
(* this is useless but nice: see [1] Definition 5.3.3 *)
| Lambda n m ⇒ (Ki (n::G) m)[0≝Sort 0]
| App m n    ⇒ Ki G m
].

interpretation "CC2FO: K interpretation (term)" 'IK t L = (Ki L t).

lemma ki_prod_3: ∀n,G. ║n║_[║G║] = 3 → 
                 ∀m. 𝕂{Prod n m}_[G] = Prod (𝕂{n}_[G]) (𝕂{m}_[n::G]).
#n #G #H #m normalize >H -H //
qed.

lemma ki_prod_not_3: ∀n,G. ║n║_[║G║] ≠ 3 →
                     ∀m. 𝕂{Prod n m}_[G] =  𝕂{m}_[n::G][0≝Sort 0].
#n #G #H #m normalize >(not_eq_to_eqb_false … H) -H //
qed.

(* replacement for the K interpretation *)
lemma ki_repl: ∀t,G1,G2. ║G1║ = ║G2║ → 𝕂{t}_[G1] = 𝕂{t}_[G2]. 
#t elim t -t //
[ #m #n #IHm #_ #G1 #G2 #HG12 >(IHm … HG12) //
| #n #m #_ #IHm #G1 #G2 #HG12 normalize >(IHm ? (n::G2)) //
| #n #m #IHn #IHm #G1 #G2 #HG12 @(eqb_elim (║n║_[║G1║]) 3) #Hdeg
  [ >(ki_prod_3 … Hdeg) >HG12 in Hdeg #Hdeg >(ki_prod_3 … Hdeg) /3/
  | >(ki_prod_not_3 … Hdeg) >HG12 in Hdeg #Hdeg >(ki_prod_not_3 … Hdeg) /3/
  ]
]
qed.

(* weakeing and thinning lemma for the K interpretation *)
(* NOTE: >commutative_plus comes from |a::b| ↦ S |b| rather than |b| + 1 *)
lemma ki_lift: ∀p,G,Gp. p = |Gp| → ∀t,k,Gk. k = |Gk| →
                              𝕂{lift t k p}_[(Lift Gk p) @ Gp @ G] =  lift (𝕂{t}_[Gk @ G]) k p.
#p #G #Gp #HGp #t elim t -t //
[ #i #k #Gk #HGk @(leb_elim (S i) k) #Hik
  [ >(lift_rel_lt … Hik) // | >(lift_rel_not_le … Hik) // ]
| #m #n #IHm #_ #k #Gk #HGk >IHm //
| #n #m #_ #IHm #k #Gk #HGk normalize <cons_append_assoc <Lift_cons //
  >(IHm … (? :: ?)) // >commutative_plus /2/
| #n #m #IHn #IHm #k #Gk #HGk >lift_prod 
  @(eqb_elim (║lift n k p║_[║Lift Gk p @Gp@G║]) 3) #Hdeg
  [ >(ki_prod_3 … Hdeg) <cons_append_assoc <Lift_cons //
    >append_Deg in Hdeg >append_Deg >deg_lift /2/ >DegHd_Lift /2/
    <append_Deg #Hdeg >(ki_prod_3 … Hdeg)
    >IHn // >(IHm … (? :: ?)) // >commutative_plus /2/
  | >(ki_prod_not_3 … Hdeg) <cons_append_assoc <Lift_cons //
    >append_Deg in Hdeg >append_Deg >deg_lift /2/ >DegHd_Lift /2/
    <append_Deg #Hdeg >(ki_prod_not_3 … Hdeg)
    >(IHm … (? :: ?)) // >commutative_plus /2/
  ]
]
qed.

(* substitution lemma for the K interpretation *)
(* NOTE: >commutative_plus comes from |a::b| ↦ S |b| rather than |b| + 1 *)
lemma ki_subst: ∀v,w,G. [║v║_[║G║]] = ║[w]║*_[║G║] →
                ∀t,k,Gk. k = |Gk| →
                                𝕂{t[k≝v]}_[Gk @ G] =  𝕂{t}_[Lift Gk 1 @ [w] @ G][k≝𝕂{v}_[G]].
#v #w #G #Hvw #t elim t -t //
[ #i #k #Gk #HGk @(leb_elim (S i) k) #H1ik
  [ >(subst_rel1 … H1ik) >(subst_rel1 … H1ik) //
  | @(eqb_elim i k) #H2ik
    [ >H2ik in H1ik -H2ik i #H1ik >subst_rel2 >subst_rel2
      >(ki_lift ? ? ? ? ? ? ([])) //
    | lapply (arith4 … H1ik H2ik) -H1ik H2ik #Hik
      >(subst_rel3 … Hik) >(subst_rel3 … Hik) //
    ]
  ]
| #m #n #IHm #_ #k #Gk #HGk >IHm //
| #n #m #_ #IHm #k #Gk #HGk normalize >(IHm … (? :: ?));
  [ >subst_lemma_comm >(Lift_cons … HGk) >ki_repl /2 by Deg_lift_subst/
  | >commutative_plus /2/
  ]
| #n #m #IHn #IHm #k #Gk #HGk >subst_prod
  @(eqb_elim (║n║_[║Lift Gk 1@[w]@G║]) 3) #Hdeg
  [ >(ki_prod_3 … Hdeg) >append_Deg in Hdeg >append_Deg >DegHd_Lift //
    <Hvw <(deg_subst … k); [2: /2/ ] <append_Deg #Hdeg
    >(ki_prod_3 … Hdeg) >IHn // >(IHm … (? :: ?));
    [ >(Lift_cons … HGk) >(ki_repl … m); /2 by Deg_lift_subst/
    | >commutative_plus /2/
    ]
  | >(ki_prod_not_3 … Hdeg) >append_Deg in Hdeg >append_Deg >DegHd_Lift //
    <Hvw <(deg_subst … k); [2: /2/ ] <append_Deg #Hdeg
    >(ki_prod_not_3 … Hdeg) >(IHm … (? :: ?));
    [ >subst_lemma_comm >(Lift_cons … HGk) >ki_repl /2 by Deg_lift_subst/
    | >commutative_plus /2/
    ]
  ]
]
qed.

lemma ki_subst_0: ∀v,w,G. [║v║_[║G║]] = ║[w]║*_[║G║] →
                  ∀t.  𝕂{t[0≝v]}_[G] = 𝕂{t}_[w::G][0≝𝕂{v}_[G]].
#v #w #G #Hvw #t @(ki_subst ?????? ([])) //
qed.

(* The K interpretation of a context ******************************************)

(* the interpretation of a λPω-context G *)
let rec KI G ≝ match G with
[ nil      ⇒ nil …
| cons t F ⇒ if_then_else ? (eqb (║t║_[║F║]) 3) (𝕂{t}_[F] :: KI F) (KI F)
].

interpretation "CC2FO: K interpretation (context)" 'IK G = (KI G).
*)
