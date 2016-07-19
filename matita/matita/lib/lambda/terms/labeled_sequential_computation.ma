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

include "lambda/terms/sequential_computation.ma".

(* ABSTRACT LABELED SEQUENTIAL COMPUTATION (MULTISTEP) **********************)

definition l_sreds: ∀S. (S→relation term) → list S → relation term ≝
                    λS,R. lstar … R.

lemma sreds_l_sreds: ∀S,R. (∀M,N. M ↦ N → ∃a. R a M N) →
                     ∀M,N. M ↦* N → ∃l. l_sreds S R l M N.
#S #R #HR #M #N #H elim H -N
[ #N #N0 #_ #HN0 * #l #HMN
  elim (HR … HN0) -HR -HN0 /3 width=5/
| /2 width=2/
]
qed-.

lemma l_sreds_inv_sreds: ∀S,R. (∀a,M,N. R a M N → M ↦ N) →
                         ∀l,M,N. l_sreds S R l M N → M ↦* N.
#S #R #HR #l #M #N #H elim H -N // /3 by star_compl/
qed-.

(* Note: "|s|" should be unparetesized *)
lemma l_sreds_fwd_mult: ∀S,R. (∀a,M,N. R a M N → M ↦ N) →
                        ∀l,M1,M2. l_sreds S R l M1 M2 →
                        ♯{M2} ≤ ♯{M1} ^ (2 ^ (|l|)).
#S #R #HR #l #M1 #M2 #H @(lstar_ind_l … l M1 H) -l -M1 normalize //
#a #l #M1 #M #HM1 #_ #IHM2
lapply (HR … HM1) -HR -a #HM1
lapply (sred_fwd_mult … HM1) #HM1
@(transitive_le … IHM2) -M2
/3 width=1 by le_exp1, lt_O_exp, lt_to_le/ (**) (* auto: slow without trace *)
qed-.
