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

include "lambda/subterms/booleanized.ma".
include "lambda/paths/labeled_sequential_reduction.ma".
include "lambda/paths/standard_order.ma".

(* PATH-LABELED STANDARD REDUCTION ON SUBTERMS (SINGLE STEP) ****************)

(* Note: this is standard reduction on marked redexes,
         left residuals are unmarked in the reductum
*)
inductive pl_st: path → relation subterms ≝
| pl_st_beta   : ∀V,T. pl_st (◊) ({⊤}@V.{⊤}𝛌.T) ([↙V]T)
| pl_st_abst   : ∀b,p,T1,T2. pl_st p T1 T2 → pl_st (rc::p) ({b}𝛌.T1) ({⊥}𝛌.T2) 
| pl_st_appl_sn: ∀b,p,V1,V2,T. pl_st p V1 V2 → pl_st (sn::p) ({b}@V1.T) ({⊥}@V2.{⊥}⇕T)
| pl_st_appl_dx: ∀b,p,V,T1,T2. pl_st p T1 T2 → pl_st (dx::p) ({b}@V.T1) ({b}@V.T2)
.

interpretation "path-labeled standard reduction"
    'Std F p G = (pl_st p F G).

notation "hvbox( F break Ⓡ ↦ [ term 46 p ] break term 46 G )"
   non associative with precedence 45
   for @{ 'Std $F $p $G }.

lemma pl_st_fwd_pl_sred: ∀p,F1,F2. F1 Ⓡ↦[p] F2 → ⇓F1 ↦[p] ⇓F2.
#p #F1 #F2 #H elim H -p -F1 -F2 normalize /2 width=1/
qed-.

lemma pl_st_inv_vref: ∀p,F,G. F Ⓡ↦[p] G → ∀b,i. {b}#i = F → ⊥.
#p #F #G #HFG #b #i #H
lapply (pl_st_fwd_pl_sred … HFG) -HFG #HFG
lapply (eq_f … carrier … H) -H normalize #H
/2 width=6 by pl_sred_inv_vref/
qed-.

lemma pl_st_inv_abst: ∀p,F,G. F Ⓡ↦[p] G → ∀c,U1. {c}𝛌.U1 = F →
                      ∃∃q,U2. U1 Ⓡ↦[q] U2 & rc::q = p & {⊥}𝛌.U2 = G.
#p #F #G * -p -F -G
[ #V #T #c #U1 #H destruct
| #b #p #T1 #T2 #HT12 #c #U1 #H destruct /2 width=5/
| #b #p #V1 #V2 #T #_ #c #U1 #H destruct
| #b #p #V #T1 #T2 #_ #c #U1 #H destruct
]
qed-.

lemma pl_st_inv_appl: ∀p,F,G. F Ⓡ↦[p] G → ∀c,W,U. {c}@W.U = F →
                      ∨∨ (∃∃U0. ⊤ = c & ◊ = p & {⊤}𝛌.U0 = U & [↙W] U0 = G)
                       | (∃∃q,W0. sn::q = p & W Ⓡ↦[q] W0 & {⊥}@W0.{⊥}⇕U = G)
                       | (∃∃q,U0. dx::q = p & U Ⓡ↦[q] U0 & {c}@W.U0 = G).
#p #F #G * -p -F -G
[ #V #T #c #W #U #H destruct /3 width=3/
| #b #p #T1 #T2 #_ #c #W #U #H destruct
| #b #p #V1 #V2 #T #HV12 #c #W #U #H destruct /3 width=5/
| #b #p #V #T1 #T2 #HT12 #c #W #U #H destruct /3 width=5/
]
qed-.

lemma pl_st_fwd_abst: ∀p,F,G. F Ⓡ↦[p] G → ∀c,U2. {c}𝛌.U2 = G →
                      ◊ = p ∨ ∃q. rc::q = p.
#p #F #G * -p -F -G
[ /2 width=1/
| /3 width=2/
| #b #p #V1 #V2 #T #_ #c #U2 #H destruct
| #b #p #V #T1 #T2 #_ #c #U2 #H destruct
]
qed-.

lemma pl_st_inv_nil: ∀p,F,G. F Ⓡ↦[p] G → ◊ = p →
                     ∃∃V,T. {⊤}@V.{⊤} 𝛌.T = F & [↙V] T = G.
#p #F #G * -p -F -G
[ #V #T #_ destruct /2 width=4/
| #b #p #T1 #T2 #_ #H destruct
| #b #p #V1 #V2 #T #_ #H destruct
| #b #p #V #T1 #T2 #_ #H destruct
]
qed-.

lemma pl_st_inv_rc: ∀p,F,G. F Ⓡ↦[p] G → ∀q. rc::q = p →
                    ∃∃b,T1,T2. T1 Ⓡ↦[q] T2 & {b}𝛌.T1 = F & {⊥}𝛌.T2 = G.
#p #F #G * -p -F -G
[ #V #T #q #H destruct
| #b #p #T1 #T2 #HT12 #q #H destruct /2 width=6/
| #b #p #V1 #V2 #T #_ #q #H destruct
| #b #p #V #T1 #T2 #_ #q #H destruct
]
qed-.

lemma pl_st_inv_sn: ∀p,F,G. F Ⓡ↦[p] G → ∀q. sn::q = p →
                    ∃∃b,V1,V2,T. V1 Ⓡ↦[q] V2 & {b}@V1.T = F & {⊥}@V2.{⊥}⇕T = G.
#p #F #G * -p -F -G
[ #V #T #q #H destruct
| #b #p #T1 #T2 #_ #q #H destruct
| #b #p #V1 #V2 #T #HV12 #q #H destruct /2 width=7/
| #b #p #V #T1 #T2 #_ #q #H destruct
]
qed-.

lemma pl_st_inv_dx: ∀p,F,G. F Ⓡ↦[p] G → ∀q. dx::q = p →
                    ∃∃b,V,T1,T2. T1 Ⓡ↦[q] T2 & {b}@V.T1 = F & {b}@V.T2 = G.
#p #F #G * -p -F -G
[ #V #T #q #H destruct
| #b #p #T1 #T2 #_ #q #H destruct
| #b #p #V1 #V2 #T #_ #q #H destruct
| #b #p #V #T1 #T2 #HT12 #q #H destruct /2 width=7/
]
qed-.

lemma pl_st_inv_pl_sred: ∀p. in_whd p → ∀M1,F2. {⊤}⇑M1 Ⓡ↦[p] F2 →
                         ∃∃M2. M1 ↦[p] M2 & {⊤}⇑M2 = F2.
#p @(in_whd_ind … p) -p
[ #M1 #F2 #H
  elim (pl_st_inv_nil … H …) -H // #V #T #HM1 #H
  elim (boolean_inv_appl … (sym_eq … HM1)) -HM1 #B #N #_ #HB #HN #HM1
  elim (boolean_inv_abst … HN) -HN #A #_ #HA #HN destruct /2 width=3/
| #p #_ #IHp #M1 #F2 #H
  elim (pl_st_inv_dx … H …) -H [3: // |2:skip ] #b #V #T1 #T2 #HT12 #HM1 #H (**) (* simplify line *)
  elim (boolean_inv_appl … (sym_eq … HM1)) -HM1 #B #A #Hb #HB #HA #HM1 destruct
  elim (IHp … HT12) -IHp -HT12 #C #HAC #H destruct
  @(ex2_intro … (@B.C)) // /2 width=1/ (**) (* auto needs some help here *)
]
qed-.

lemma pl_st_lift: ∀p. sliftable (pl_st p).
#p #h #F1 #F2 #H elim H -p -F1 -F2 /2 width=1/
[ #V #T #d normalize <sdsubst_slift_le //
| #b #p #V1 #V2 #T #_ #IHV12 #d
  whd in ⊢ (??%%); <booleanized_lift /2 width=1/ (**) (* auto needs some help here *)
]
qed.

lemma pl_st_inv_lift: ∀p. sdeliftable_sn (pl_st p).
#p #h #G1 #G2 #H elim H -p -G1 -G2
[ #W #U #d #F1 #H
  elim (slift_inv_appl … H) -H #V #F #H0 #HF #H destruct
  elim (slift_inv_abst … HF) -HF #T #H0 #H destruct /3 width=3/
| #b #p #U1 #U2 #_ #IHU12 #d #F1 #H
  elim (slift_inv_abst … H) -H #T1 #HTU1 #H
  elim (IHU12 … HTU1) -U1 #T2 #HT12 #HTU2 destruct
  @(ex2_intro … ({⊥}𝛌.T2)) // /2 width=1/
| #b #p #W1 #W2 #U1 #_ #IHW12 #d #F1 #H
  elim (slift_inv_appl … H) -H #V1 #T #HVW1 #H1 #H2
  elim (IHW12 … HVW1) -W1 #V2 #HV12 #HVW2 destruct
  @(ex2_intro … ({⊥}@V2.{⊥}⇕T)) [ /2 width=1/ ]
  whd in ⊢ (??%%); // (**) (* auto needs some help here *)
| #b #p #W1 #U1 #U2 #_ #IHU12 #d #F1 #H
  elim (slift_inv_appl … H) -H #V #T1 #H1 #HTU1 #H2
  elim (IHU12 … HTU1) -U1 #T2 #HT12 #HTU2 destruct
  @(ex2_intro … ({b}@V.T2)) // /2 width=1/
]
qed-.

lemma pl_st_dsubst: ∀p. sdsubstable_f_dx … (booleanized ⊥) (pl_st p).
#p #W1 #F1 #F2 #H elim H -p -F1 -F2 /2 width=1/
[ #W2 #T #d normalize >sdsubst_sdsubst_ge //
| #b #p #V1 #V2 #T #_ #IHV12 #d
  whd in ⊢ (??%%); <(booleanized_booleanized ⊥) in ⊢ (???(???%)); <booleanized_dsubst /2 width=1/ (**) (* auto needs some help here *)
]
qed.

lemma pl_st_inv_empty: ∀p,F1,F2. F1 Ⓡ↦[p] F2 → ∀M1. {⊥}⇑M1 = F1 → ⊥.
#p #F1 #F2 #H elim H -p -F1 -F2
[ #V #T #M1 #H
  elim (boolean_inv_appl … H) -H #B #A #H destruct
| #b #p #T1 #T2 #_ #IHT12 #M1 #H
  elim (boolean_inv_abst … H) -H /2 width=2/
| #b #p #V1 #V2 #T #_ #IHV12 #M1 #H
  elim (boolean_inv_appl … H) -H /2 width=2/
| #b #p #V #T1 #T2 #_ #IHT12 #M1 #H
  elim (boolean_inv_appl … H) -H /2 width=2/
]
qed-.

theorem pl_st_mono: ∀p. singlevalued … (pl_st p).
#p #F #G1 #H elim H -p -F -G1
[ #V #T #G2 #H elim (pl_st_inv_nil … H …) -H //
  #W #U #H #HG2 destruct //
| #b #p #T1 #T2 #_ #IHT12 #G2 #H elim (pl_st_inv_rc … H …) -H [3: // |2: skip ] (**) (* simplify line *)
  #c #U1 #U2 #HU12 #H #HG2 destruct /3 width=1/
| #b #p #V1 #V2 #T #_ #IHV12 #G2 #H elim (pl_st_inv_sn … H …) -H [3: // |2: skip ] (**) (* simplify line *)
  #c #W1 #W2 #U #HW12 #H #HG2 destruct /3 width=1/
| #b #p #V #T1 #T2 #_ #IHT12 #G2 #H elim (pl_st_inv_dx … H …) -H [3: // |2: skip ] (**) (* simplify line *)
  #c #W #U1 #U2 #HU12 #H #HG2 destruct /3 width=1/
]
qed-.

theorem pl_st_fwd_sle: ∀p1,F1,F. F1 Ⓡ↦[p1] F →
                       ∀p2,F2. F Ⓡ↦[p2] F2 → p1 ≤ p2.
#p1 #F1 #F #H elim H -p1 -F1 -F //
[ #b #p #T1 #T #_ #IHT1 #p2 #F2 #H elim (pl_st_inv_abst … H …) -H [3: // |2,4: skip ] (**) (* simplify line *)
  #q #T2 #HT2 #H1 #H2 destruct /3 width=2/
| #b #p #V1 #V #T #_ #IHV1 #p2 #F2 #H elim (pl_st_inv_appl … H …) -H [7: // |2,3,4: skip ] * (**) (* simplify line *)
  [ #U #H destruct
  | #q #V2 #H1 #HV2 #H2 destruct /3 width=2/
  | #q #U #_ #H elim (pl_st_inv_empty … H …) [ // | skip ] (**) (* simplify line *)
  ]
| #b #p #V #T1 #T #HT1 #IHT1 #p2 #F2 #H elim (pl_st_inv_appl … H …) -H [7: // |2,3,4: skip ] * (**) (* simplify line *)
  [ #U #_ #H1 #H2 #_ -b -V -F2 -IHT1
    elim (pl_st_fwd_abst … HT1 … H2) // -H1 * #q #H
    elim (pl_st_inv_rc … HT1 … H) -HT1 -H #b #U1 #U2 #_ #_ #H -b -q -T1 -U1 destruct
  | #q #V2 #H1 #_ #_ -b -F2 -T1 -T -V -V2 destruct //
  | #q #T2 #H1 #HT2 #H2 -b -F2 -T1 -V /3 width=2/
  ]
]
qed-.
