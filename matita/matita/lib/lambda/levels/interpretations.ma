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

include "lambda/notation/functions/forward_1.ma".
include "lambda/notation/functions/forward_3.ma".
include "lambda/notation/functions/backward_1.ma".
include "lambda/notation/functions/backward_3.ma".
include "lambda/terms/iterated_abstraction.ma".
include "lambda/levels/iterated_abstraction.ma".

(* INTERPRETATIONS **********************************************************)

let rec bylevel h d M on M ≝ match M with
[ VRef i   ⇒ {h}§(tri … i d (d-i-1) i i)
| Abst A   ⇒ bylevel (h+1) (d+1) A
| Appl C A ⇒ {h}@(bylevel 0 d C).(bylevel 0 d A)
].

interpretation "forward interpretation (term by depth) general"
   'Forward h d M = (bylevel h d M).

interpretation "forward interpretation (term by depth)"
   'Forward M = (bylevel O O M).

lemma bylevel_abst: ∀i,h,d,M. ⇑[d, h] 𝛌i. M = ⇑[i+d, i+h] M.
#i elim i -i normalize //
qed.

let rec bydepth h d M on M ≝ match M with
[ LVRef i e   ⇒ 𝛌i.#(tri … e (d+i-h) (d+i-h-e-1) e e)
| LAppl i C A ⇒ 𝛌i.@(bydepth h (d+i) C).(bydepth h (d+i) A)
].

interpretation "backward interpretation (term by level) general"
   'Backward h d M = (bydepth h d M).

interpretation "backward interpretation (term by level)"
   'Backward M = (bydepth O O M).

lemma by_depth_level_gen: ∀M,e,d,h. d ≤ e + h → ⇓[e, e+h-d] ⇑[d, h] M = 𝛌h.M.
#M elim M -M normalize
[ #i #e #d #h #Hdeh >(minus_minus_m_m … Hdeh)
  elim (lt_or_eq_or_gt i d) #Hid
  [ >(tri_lt ???? … Hid) >(tri_lt ???? d (d-i-1))
    /5 width=1 by minus_le_minus_minus_comm, monotonic_lt_minus_l, eq_f/ 
  | destruct >(tri_eq ???? …) >(tri_eq ???? …) //
  | >(tri_gt ???? … Hid) >(tri_gt ???? … Hid) //
  ]
| #A #IHA #e #d #h #Hdeh lapply (IHA e (d+1) (h+1) ?) -IHA
  /2 width=1 by le_S_S, eq_f2/
| #C #A #IHC #IHA #e #d #h #Hdeh
  lapply (IHC (e+h) d 0 ?) -IHC // lapply (IHA (e+h) d 0 ?) -IHA //
  normalize /2 width=1 by/
]
qed-.

theorem by_depth_level: ∀M. ⇓⇑M = M.
#M lapply (by_depth_level_gen M 0 0 0 ?) normalize //
qed.

lemma by_level_depth_gen: ∀M,e,d,h. d ≤ e → ⇑[d, h] ⇓[e, e-d] M = 𝛌h.M.
#M elim M -M
[ #i #k #e #d #h #Hde >bylevel_abst normalize >(minus_plus_minus_l … Hde)
  elim (lt_or_eq_or_gt k (i+d)) #Hkid
  [ >(tri_lt ???? … Hkid) >(tri_lt ???? (i+d) (i+d-k-1))
    /5 width=1 by minus_le_minus_minus_comm, monotonic_lt_minus_l, eq_f/ 
  | destruct >(tri_eq ???? …) >(tri_eq ???? …) //
  | >(tri_gt ???? … Hkid) >(tri_gt ???? … Hkid) //
  ]
| #i #C #A #IHC #IHA #e #d #h #Hdeh >bylevel_abst normalize
  lapply (IHC (e+i) (i+d) 0 ?) -IHC /2 width=1 by monotonic_le_plus_r/
  lapply (IHA (e+i) (i+d) 0 ?) -IHA /2 width=1 by monotonic_le_plus_r/
  /3 width=1 by eq_f3, eq_f2/
]
qed-.

theorem by_level_depth: ∀M. ⇑⇓M = M.
#M lapply (by_level_depth_gen M 0 0 0 ?) //
qed.
