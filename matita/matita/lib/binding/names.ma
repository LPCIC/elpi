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

include "basics/logic.ma".
include "basics/lists/in.ma".
include "basics/types.ma".

(*interpretation "list membership" 'mem x l = (in_list ? x l).*)

record Nset : Type[1] ≝
{
  (* carrier is specified as a coercion: when an object X of type Nset is
     given, but something of type Type is expected, Matita will insert a
     hidden coercion: the user sees "X", but really means "carrier X"     *)
  carrier :> DeqSet;
  N_fresh : list carrier → carrier;
  p_fresh : ∀l.N_fresh l ∉ l
}.

definition maxlist ≝
 λl.foldr ?? (λx,acc.max x acc) 0 l.

definition natfresh ≝ λl.S (maxlist l).

lemma le_max_1 : ∀x,y.x ≤ max x y. /2/
qed.

lemma le_max_2 : ∀x,y.y ≤ max x y. /2/
qed.

lemma le_maxlist : ∀l,x.x ∈ l → x ≤ maxlist l.
#l elim l
[#x #Hx @False_ind cases (not_in_list_nil ? x) #H1 /2/
|#y #tl #IH #x #H1 change with (max ??) in ⊢ (??%);
 cases (in_list_cons_case ???? H1);#H2;
 [ >H2 @le_max_1
 | whd in ⊢ (??%); lapply (refl ? (leb y (maxlist tl)));
   cases (leb y (maxlist tl)) in ⊢ (???% → %);#H3
   [ @IH //
   | lapply (IH ? H2) #H4
     lapply (leb_false_to_not_le … H3) #H5
     lapply (not_le_to_lt … H5) #H6
     @(transitive_le … H4)
     @(transitive_le … H6) %2 %
   ]
 ]
]
qed.

(* prove freshness for nat *)
lemma lt_l_natfresh_l : ∀l,x.x ∈ l → x < natfresh l.
#l #x #H1 @le_S_S /2/
qed.

(*naxiom p_Xfresh : ∀l.∀x:Xcarr.x ∈ l → x ≠ ntm (Xfresh l) ∧ x ≠ ntp (Xfresh l).*)
lemma p_natfresh : ∀l.natfresh l ∉ l.
#l % #H1 lapply (lt_l_natfresh_l … H1) #H2
cases (lt_to_not_eq … H2) #H3 @H3 %
qed.

include "basics/finset.ma".

definition X : Nset ≝ mk_Nset DeqNat ….
[ @natfresh
| @p_natfresh
]
qed.