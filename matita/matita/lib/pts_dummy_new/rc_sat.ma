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

include "pts_dummy/sn.ma".
(*
(* REDUCIBILITY CANDIDATES ****************************************************)

(* The reducibility candidate (r.c.) ******************************************)

(* We use saturated subsets of strongly normalizing terms [1]
 * rather than standard reducibility candidates [2].
 * The benefit is that reduction is not needed to define such subsets.
 * [1] Geuvers, H. 1994. A Short and Flexible Proof of Strong Normalization for the Calculus of Constructions.
 * [2] Barras, B. 1996. Coq en Coq. Rapport de Recherche 3026, INRIA.
 *)
record RC : Type[0] ≝ {
   mem : T → Prop;
   cr1 : CR1 mem;
   sat0: SAT0 mem;
   sat1: SAT1 mem;
   sat2: SAT2 mem;
   sat3: SAT3 mem;  (* we add the clusure by rev dapp *)
   sat4: SAT4 mem   (* we add the clusure by dummies *) 
}.

(* HIDDEN BUG:
 * if SAT0 and SAT1 are expanded,
 * the projections sat0 and sat1 are not generated
 *)

interpretation "membership (reducibility candidate)" 'mem A R = (mem R A).

(* the r.c. of all s.n. terms *)
definition snRC: RC ≝ mk_RC SN ….
/2/ qed.

(*
(* a generalization of mem on lists *)
let rec memc E l on l : Prop ≝ match l with
   [ nil ⇒ True
   | cons hd tl ⇒ match E with
      [ nil      ⇒ hd ∈ snRC ∧ memc E tl
      | cons C D ⇒ hd ∈ C ∧ memc D tl
      ]
   ].

interpretation
   "componentwise membership (context of reducibility candidates)"
   'mem l H = (memc H l).
*)
(* extensional equality of r.c.'s *********************************************)

definition rceq: RC → RC → Prop ≝ 
                 λC1,C2. ∀M. (M ∈ C1 → M ∈ C2) ∧ (M ∈ C2 → M ∈ C1).

interpretation
   "extensional equality (reducibility candidate)"
   'Eq C1 C2 = (rceq C1 C2).

definition rceql ≝ λl1,l2. all2 … rceq l1 l2.

interpretation
   "extensional equality (context of reducibility candidates)"
   'Eq C1 C2 = (rceql C1 C2).

lemma reflexive_rceq: reflexive … rceq.
/2/ qed.

lemma symmetric_rceq: symmetric … rceq.
#x #y #H #M elim (H M) -H /3/
qed.

lemma transitive_rceq: transitive … rceq.
#x #y #z #Hxy #Hyz #M elim (Hxy M) -Hxy; elim (Hyz M) -Hyz /4/
qed.
(*
theorem reflexive_rceql: reflexive … rceql.
#l (elim l) /2/
qed.
*)
(* HIDDEN BUG:
 * Without the type specification, this statement has two interpretations
 * but matita does not complain
 *)
lemma mem_rceq_trans: ∀(M:T). ∀C1,C2. M ∈ C1 → C1 ≅ C2 → M ∈ C2.
#M #C1 #C2 #H1 #H12 elim (H12 M) -H12 /2/
qed.
(*
(* NOTE: hd_repl and tl_repl are proved essentially by the same script *)
lemma hd_repl: ∀C1,C2. C1 ≅ C2 → ∀l1,l2. l1 ≅ l2 → hd ? l1 C1 ≅ hd ? l2 C2.
#C1 #C2 #QC #l1 (elim l1) -l1 [ #l2 #Q >Q // ]
#hd1 #tl1 #_ #l2 (elim l2) -l2 [ #Q elim Q ]
#hd2 #tl2 #_ #Q elim Q //
qed.

lemma tl_repl: ∀l1,l2. l1 ≅ l2 → tail ? l1 ≅ tail ? l2.
#l1 (elim l1) -l1 [ #l2 #Q >Q // ]
#hd1 #tl1 #_ #l2 (elim l2) -l2 [ #Q elim Q ]
#hd2 #tl2 #_ #Q elim Q //
qed.

lemma nth_repl: ∀C1,C2. C1 ≅ C2 → ∀i,l1,l2. l1 ≅ l2 →
                  nth i ? l1 C1 ≅ nth i ? l2 C2.
#C1 #C2 #QC #i (elim i) /3/
qed.
*)
(* the r.c. for a (dependent) product type. ***********************************)

definition dep_mem ≝ λB,C,M. ∀N. N ∈ B → App M N ∈ C.

lemma dep_cr1: ∀B,C. CR1 (dep_mem B C).
#B #C #M #Hdep (lapply (Hdep (Sort 0) ?)) -Hdep /3/ @SAT0_sort //
qed.

lemma dep_sat0: ∀B,C. SAT0 (dep_mem B C).
/5/ qed.

lemma dep_sat1: ∀B,C. SAT1 (dep_mem B C).
/5/ qed.

(* NOTE: @sat2 is not needed if append_cons is enabled *)
lemma dep_sat2: ∀B,C. SAT2 (dep_mem B C).
#B #C #N #L #M #l #HN #HL #HM #K #HK <appl_append @sat2 /2/
qed.

lemma dep_sat3: ∀B,C. SAT3 (dep_mem B C).
#B #C #M #N #l #H #L #HL <appl_append @sat3 /2/
qed.

lemma dep_sat4: ∀B,C. SAT4 (dep_mem B C).
#B #C #N #HN #M #HM @SAT3_1 /3/ 
qed.

definition depRC: RC → RC → RC ≝ λB,C. mk_RC (dep_mem B C) ….
/2/ qed.

lemma dep_repl: ∀B1,B2,C1,C2. B1 ≅ B2 → C1 ≅ C2 →
                depRC B1 C1 ≅ depRC B2 C2.
#B1 #B2 #C1 #C2 #QB #QC #M @conj #H1 #N #H2
[ lapply (symmetric_rceq … QB) -QB | lapply (symmetric_rceq … QC) -QC ] /4/
qed.

(* the union of two r.c.'s. ***************************************************)

definition lor_mem ≝ λB,C,M. M ∈ B ∨ M ∈ C.

lemma lor_cr1: ∀B,C. CR1 (lor_mem B C).
#B #C #M #Hlor elim Hlor -Hlor #HM /2/
qed.

lemma lor_sat0: ∀B,C. SAT0 (lor_mem B C).
/3/ qed.

lemma lor_sat1: ∀B,C. SAT1 (lor_mem B C).
/3/ qed.

lemma lor_sat2: ∀B,C. SAT2 (lor_mem B C).
#B #C #N #L #M #l #HN #HL #HM elim HM -HM #HM /3/
qed.

lemma lor_sat3: ∀B,C. SAT3 (lor_mem B C).
#B #C #N #l1 #l2 #HN elim HN -HN #HN /3/
qed.

lemma lor_sat4: ∀B,C. SAT4 (lor_mem B C).
#B #C #N #HN elim HN -HN #HN /3/
qed.

definition lorRC: RC → RC → RC ≝ λB,C. mk_RC (lor_mem B C) ….
/2/ qed.
*)
