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

include "finite_lambda/terms_and_types.ma".

(* some auxiliary lemmas *)

lemma nth_to_default: ∀A,l,n,d. 
  |l| ≤ n → nth n A l d = d.
#A #l elim l [//] #a #tl #Hind #n cases n
  [#d normalize #H @False_ind @(absurd … H) @lt_to_not_le //
  |#m #d normalize #H @Hind @le_S_S_to_le @H
  ]
qed.

lemma mem_nth: ∀A,l,n,d. 
  n < |l|  → mem ? (nth n A l d) l.
#A #l elim l   
  [#n #d normalize #H @False_ind @(absurd … H) @lt_to_not_le //
  |#a #tl #Hind * normalize 
    [#_ #_ %1 //| #m #d #HSS %2 @Hind @le_S_S_to_le @HSS]
  ]
qed.

lemma nth_map: ∀A,B,l,f,n,d1,d2. 
  n < |l| → nth n B (map … f l) d1 = f (nth n A l d2).
#n #B #l #f elim l 
  [#m #d1 #d2 normalize #H @False_ind @(absurd … H) @lt_to_not_le //
  |#a #tl #Hind #m #d1 #d2 cases m normalize // 
   #m1 #H @Hind @le_S_S_to_le @H
  ]
qed.



(* end of auxiliary lemmas *)

let rec to_T O D ty on ty: FinSet_of_FType O D ty → T O D ≝ 
  match ty return (λty.FinSet_of_FType O D ty → T O D) with 
  [atom o ⇒ λa.Val O D o a
  |arrow ty1 ty2 ⇒ λa:FinFun ??.Vec O D ty1  
    (map ((FinSet_of_FType O D ty1)×(FinSet_of_FType O D ty2)) 
     (T O D) (λp.to_T O D ty2 (snd … p)) (pi1 … a))
  ]
.

lemma is_closed_to_T: ∀O,D,ty,a. is_closed O D 0 (to_T O D ty a).
#O #D #ty elim ty //
#ty1 #ty2 #Hind1 #Hind2 #a normalize @cvec #m #Hmem
lapply (mem_map ????? Hmem) * #a1 * #H1 #H2 <H2 @Hind2 
qed.

axiom inj_to_T: ∀O,D,ty,a1,a2. to_T O D ty a1 = to_T O D ty a2 → a1 = a2. 
(* complicata 
#O #D #ty elim ty 
  [#o normalize #a1 #a2 #H destruct //
  |#ty1 #ty2 #Hind1 #Hind2 * #l1 #Hl1 * #l2 #Hl2 normalize #H destruct -H
   cut (l1=l2) [2: #H generalize in match Hl1; >H //] -Hl1 -Hl2
   lapply e0 -e0 lapply l2 -l2 elim l1 
    [#l2 cases l2 normalize [// |#a1 #tl1 #H destruct]
    |#a1 #tl1 #Hind #l2 cases l2 
      [normalize #H destruct
      |#a2 #tl2 normalize #H @eq_f2
        [@Hind2 *)
        
let rec assoc (A:FinSet) (B:Type[0]) (a:A) l1 l2 on l1 : option B ≝
  match l1 with
  [ nil ⇒  None ?
  | cons hd1 tl1 ⇒ match l2 with
    [ nil ⇒ None ?
    | cons hd2 tl2 ⇒ if a==hd1 then Some ? hd2 else assoc A B a tl1 tl2
    ]
  ]. 
  
lemma same_assoc: ∀A,B,a,l1,v1,v2,N,N1.
  assoc A B a l1 (v1@N::v2) = Some ? N ∧ assoc A B a l1 (v1@N1::v2) = Some ? N1 
   ∨ assoc A B a l1 (v1@N::v2) = assoc A B a l1 (v1@N1::v2).
#A #B #a #l1 #v1 #v2 #N #N1 lapply v1 -v1 elim l1 
  [#v1 %2 // |#hd #tl #Hind * normalize cases (a==hd) normalize /3/]
qed.

lemma assoc_to_mem: ∀A,B,a,l1,l2,b. 
  assoc A B a l1 l2 = Some ? b → mem ? b l2.
#A #B #a #l1 elim l1
  [#l2 #b normalize #H destruct
  |#hd1 #tl1 #Hind * 
    [#b normalize #H destruct
    |#hd2 #tl2 #b normalize cases (a==hd1) normalize
      [#H %1 destruct //|#H %2 @Hind @H]
    ]
  ]
qed.

lemma assoc_to_mem2: ∀A,B,a,l1,l2,b. 
  assoc A B a l1 l2 = Some ? b → ∃l21,l22.l2=l21@b::l22.
#A #B #a #l1 elim l1
  [#l2 #b normalize #H destruct
  |#hd1 #tl1 #Hind * 
    [#b normalize #H destruct
    |#hd2 #tl2 #b normalize cases (a==hd1) normalize
      [#H %{[]} %{tl2} destruct //
      |#H lapply (Hind … H) * #la * #lb #H1 
       %{(hd2::la)} %{lb} >H1 //]
    ]
  ]
qed.

lemma assoc_map: ∀A,B,C,a,l1,l2,f,b. 
  assoc A B a l1 l2 = Some ? b → assoc A C a l1 (map ?? f l2) = Some ? (f b).
#A #B #C #a #l1 elim l1
  [#l2 #f #b normalize #H destruct
  |#hd1 #tl1 #Hind * 
    [#f #b normalize #H destruct
    |#hd2 #tl2 #f #b normalize cases (a==hd1) normalize
      [#H destruct // |#H @(Hind … H)]
    ]
  ]
qed.

(*************************** One step reduction *******************************)

inductive red (O:Type[0]) (D:O→FinSet) : T O D  →T O D → Prop ≝
  | (* we only allow beta on closed arguments *)
    rbeta: ∀P,M,N. is_closed O D 0 N →
      red O D (App O D (Lambda O D P M) N) (subst O D M 0 N)
  | riota: ∀ty,v,a,M. 
      assoc ?? a (enum (FinSet_of_FType O D ty)) v = Some ? M →
      red O D (App O D (Vec O D ty v) (to_T O D ty a)) M
  | rappl: ∀M,M1,N. red O D M M1 → red O D (App O D M N) (App O D M1 N)
  | rappr: ∀M,N,N1. red O D N N1 → red O D (App O D M N) (App O D M N1)
  | rlam: ∀ty,N,N1. red O D N N1 → red O D (Lambda O D ty N) (Lambda O D ty N1) 
  | rmem: ∀ty,M. red O D (Lambda O D ty M)
      (Vec O D ty (map ?? (λa. subst O D M 0 (to_T O D ty a)) 
      (enum (FinSet_of_FType O D ty)))) 
  | rvec: ∀ty,N,N1,v,v1. red O D N N1 → 
      red O D (Vec O D ty (v@N::v1)) (Vec O D ty (v@N1::v1)).
 
(*********************************** inversion ********************************)
lemma red_vec: ∀O,D,ty,v,M.
  red O D (Vec O D ty v) M → ∃N,N1,v1,v2.
      red O D N N1 ∧ v = v1@N::v2 ∧ M = Vec O D ty (v1@N1::v2).
#O #D #ty #v #M #Hred inversion Hred
  [#ty1 #M0 #N #Hc #H destruct
  |#ty1 #v1 #a #M0 #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#ty1 #M #M1 #_ #_ #H destruct
  |#ty1 #M0 #H destruct
  |#ty1 #N #N1 #v1 #v2 #Hred1 #_ #H destruct #_ %{N} %{N1} %{v1} %{v2} /3/
  ]
qed.
      
lemma red_lambda: ∀O,D,ty,M,N.
  red O D (Lambda O D ty M) N → 
      (∃M1. red O D M M1 ∧ N = (Lambda O D ty M1)) ∨
      N = Vec O D ty (map ?? (λa. subst O D M 0 (to_T O D ty a)) 
      (enum (FinSet_of_FType O D ty))).
#O #D #ty #M #N #Hred inversion Hred
  [#ty1 #M0 #N #Hc #H destruct
  |#ty1 #v1 #a #M0 #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#ty1 #P #P1 #redP #_ #H #H1 destruct %1 %{P1} % //
  |#ty1 #M0 #H destruct #_ %2 //
  |#ty1 #N #N1 #v1 #v2 #Hred1 #_ #H destruct
  ]
qed. 

lemma red_val: ∀O,D,ty,a,N.
  red O D (Val O D ty a) N → False.
#O #D #ty #M #N #Hred inversion Hred
  [#ty1 #M0 #N #Hc #H destruct
  |#ty1 #v1 #a #M0 #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#ty1 #N1 #N2 #_ #_ #H destruct
  |#ty1 #M0 #H destruct #_ 
  |#ty1 #N #N1 #v1 #v2 #Hred1 #_ #H destruct
  ]
qed. 

lemma red_rel: ∀O,D,n,N.
  red O D (Rel O D n) N → False.
#O #D #n #N #Hred inversion Hred
  [#ty1 #M0 #N #Hc #H destruct
  |#ty1 #v1 #a #M0 #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#ty1 #N1 #N2 #_ #_ #H destruct
  |#ty1 #M0 #H destruct #_ 
  |#ty1 #N #N1 #v1 #v2 #Hred1 #_ #H destruct
  ]
qed. 
 
(*************************** multi step reduction *****************************)
lemma star_red_appl: ∀O,D,M,M1,N. star ? (red O D) M M1 → 
  star ? (red O D) (App O D M N) (App O D M1 N).
#O #D #M #N #N1 #H elim H // 
#P #Q #Hind #HPQ #Happ %1[|@Happ] @rappl @HPQ
qed.

lemma star_red_appr: ∀O,D,M,N,N1. star ? (red O D) N N1 → 
  star ? (red O D) (App O D M N) (App O D M N1).
#O #D #M #N #N1 #H elim H // 
#P #Q #Hind #HPQ #Happ %1[|@Happ] @rappr @HPQ
qed.

lemma star_red_vec: ∀O,D,ty,N,N1,v1,v2. star ? (red O D) N N1 → 
  star ? (red O D) (Vec O D ty (v1@N::v2)) (Vec O D ty (v1@N1::v2)).
#O #D #ty #N #N1 #v1 #v2 #H elim H // 
#P #Q #Hind #HPQ #Hvec %1[|@Hvec] @rvec @HPQ
qed.

lemma star_red_vec1: ∀O,D,ty,v1,v2,v. |v1| = |v2| →
  (∀n,M. n < |v1| → star ? (red O D) (nth n ? v1 M) (nth n ? v2 M)) → 
  star ? (red O D) (Vec O D ty (v@v1)) (Vec O D ty (v@v2)).
#O #D #ty #v1 elim v1 
  [#v2 #v normalize #Hv2 >(lenght_to_nil … (sym_eq … Hv2)) normalize //
  |#N1 #tl1 #Hind * [normalize #v #H destruct] #N2 #tl2 #v normalize #HS
   #H @(trans_star … (Vec O D ty (v@N2::tl1)))
    [@star_red_vec @(H 0 N1) @le_S_S //
    |>append_cons >(append_cons ??? tl2) @(Hind… (injective_S … HS))
     #n #M #H1 @(H (S n)) @le_S_S @H1
    ]
  ]
qed.

lemma star_red_vec2: ∀O,D,ty,v1,v2. |v1| = |v2| →
  (∀n,M. n < |v1| → star ? (red O D) (nth n ? v1 M) (nth n ? v2 M)) → 
  star ? (red O D) (Vec O D ty v1) (Vec O D ty v2).
#O #D #ty #v1 #v2 @(star_red_vec1 … [ ])
qed.

lemma star_red_lambda: ∀O,D,ty,N,N1. star ? (red O D) N N1 → 
  star ? (red O D) (Lambda O D ty N) (Lambda O D ty N1).
#O #D #ty #N #N1 #H elim H // 
#P #Q #Hind #HPQ #Hlam %1[|@Hlam] @rlam @HPQ
qed.

(************************ reduction and substitution **************************)
  
lemma red_star_subst : ∀O,D,M,N,N1,i. 
  star ? (red O D) N N1 → star ? (red O D) (subst O D M i N) (subst O D M i N1).
#O #D #M #N #N1 #i #Hred lapply i -i @(T_elim … M) normalize
  [#o #a #i //
  |#i #n cases (leb n i) normalize // cases (eqb n i) normalize //
  |#P #Q #HindP #HindQ #n normalize 
   @(trans_star … (App O D (subst O D P n N1) (subst O D Q n N))) 
    [@star_red_appl @HindP |@star_red_appr @HindQ]
  |#ty #P #HindP #i @star_red_lambda @HindP
  |#ty #v #Hindv #i @star_red_vec2 [>length_map >length_map //]
   #j #Q inversion v [#_ normalize //] #a #tl #_ #Hv
   cases (true_or_false (leb (S j) (|a::tl|))) #Hcase
    [lapply (leb_true_to_le … Hcase) -Hcase #Hcase
     >(nth_map ?????? a Hcase) >(nth_map ?????? a Hcase) #_ @Hindv >Hv @mem_nth //
    |>nth_to_default 
      [2:>length_map @le_S_S_to_le @not_le_to_lt @leb_false_to_not_le //]
     >nth_to_default 
      [2:>length_map @le_S_S_to_le @not_le_to_lt @leb_false_to_not_le //] //
    ]
  ]
qed.
     
lemma red_star_subst2 : ∀O,D,M,M1,N,i. is_closed O D 0 N → 
  red O D M M1 → star ? (red O D) (subst O D M i N) (subst O D M1 i N).
#O #D #M #M1 #N #i #HNc #Hred lapply i -i elim Hred
  [#ty #P #Q #HQc #i normalize @starl_to_star @sstepl 
   [|@rbeta >(subst_closed … HQc) //] >(subst_closed … HQc) // 
    lapply (subst_lemma ?? P ?? i 0 (is_closed_mono … HQc) HNc) // 
    <plus_n_Sm <plus_n_O #H <H //
  |#ty #v #a #P #HP #i normalize >(subst_closed … (le_O_n …)) //
   @R_to_star @riota @assoc_map @HP 
  |#P #P1 #Q #Hred #Hind #i normalize @star_red_appl @Hind
  |#P #P1 #Q #Hred #Hind #i normalize @star_red_appr @Hind
  |#ty #P #P1 #Hred #Hind #i normalize @star_red_lambda @Hind
  |#ty #P #i normalize @starl_to_star @sstepl [|@rmem] 
   @star_to_starl @star_red_vec2 [>length_map >length_map >length_map //]
   #n #Q >length_map #H
   cut (∃a:(FinSet_of_FType O D ty).True) 
    [lapply H -H lapply (enum_complete (FinSet_of_FType O D ty))
     cases (enum (FinSet_of_FType O D ty)) 
      [#x normalize #H @False_ind @(absurd … H) @lt_to_not_le //
      |#x #l #_ #_ %{x} //
      ]
    ] * #a #_
   >(nth_map ?????? a H) >(nth_map ?????? Q) [2:>length_map @H] 
   >(nth_map ?????? a H) 
   lapply (subst_lemma O D P (to_T O D ty
    (nth n (FinSet_of_FType O D ty) (enum (FinSet_of_FType O D ty)) a)) 
   N i 0 (is_closed_mono … (is_closed_to_T …)) HNc) // <plus_n_O #H1 >H1
   <plus_n_Sm <plus_n_O //
  |#ty #P #Q #v #v1 #Hred #Hind #n normalize 
   <map_append <map_append @star_red_vec @Hind
  ]
qed.
   




