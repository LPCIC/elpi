(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic   
    ||A||  Library of Mathematics, developed at the Computer Science 
    ||T||  Department of the University of Bologna, Italy.           
    ||I||                                                            
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_____________________________________________________________*)

include "turing/turing.ma".

definition compare_states ≝ initN 3.

definition comp0 : compare_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition comp1 : compare_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition comp2 : compare_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).

definition trans_compare_step ≝ 
 λi,j.λsig:FinSet.λn.
 λp:compare_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 match pi1 … q with
 [ O ⇒ match nth i ? a (None ?) with
   [ None ⇒ 〈comp2,null_action sig n〉
   | Some ai ⇒ match nth j ? a (None ?) with 
     [ None ⇒ 〈comp2,null_action ? n〉
     | Some aj ⇒ if ai == aj 
         then 〈comp1,change_vec ? (S n) 
                      (change_vec ? (S n) (null_action ? n) (〈None ?,R〉) i)
                        (〈None ?,R〉) j〉
         else 〈comp2,null_action ? n〉 ]
   ]
 | S q ⇒ match q with 
   [ O ⇒ (* 1 *) 〈comp1,null_action ? n〉
   | S _ ⇒ (* 2 *) 〈comp2,null_action ? n〉 ] ].

definition compare_step ≝ 
  λi,j,sig,n.
  mk_mTM sig n compare_states (trans_compare_step i j sig n) 
    comp0 (λq.q == comp1 ∨ q == comp2).

definition R_comp_step_true ≝ 
  λi,j,sig,n.λint,outt: Vector (tape sig) (S n).
  ∃x.
   current ? (nth i ? int (niltape ?)) = Some ? x ∧
   current ? (nth j ? int (niltape ?)) = Some ? x ∧
   outt = change_vec ?? 
            (change_vec ?? int
              (tape_move_right ? (nth i ? int (niltape ?))) i)
            (tape_move_right ? (nth j ? int (niltape ?))) j.

definition R_comp_step_false ≝ 
  λi,j:nat.λsig,n.λint,outt: Vector (tape sig) (S n).
   (current ? (nth i ? int (niltape ?)) ≠ current ? (nth j ? int (niltape ?)) ∨
    current ? (nth i ? int (niltape ?)) = None ? ∨
    current ? (nth j ? int (niltape ?)) = None ?) ∧ outt = int.

lemma comp_q0_q2_null :
  ∀i,j,sig,n,v.i < S n → j < S n → 
  (nth i ? (current_chars ?? v) (None ?) = None ? ∨
   nth j ? (current_chars ?? v) (None ?) = None ?) → 
  step sig n (compare_step i j sig n) (mk_mconfig ??? comp0 v) 
  = mk_mconfig ??? comp2 v.
#i #j #sig #n #v #Hi #Hj
whd in ⊢ (? → ??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (?→??%?);
* #Hcurrent
[ @eq_f2
  [ whd in ⊢ (??(???%)?); >Hcurrent %
  | whd in ⊢ (??(????(???%))?); >Hcurrent @tape_move_null_action ]
| @eq_f2
  [ whd in ⊢ (??(???%)?); >Hcurrent cases (nth i ?? (None sig)) //
  | whd in ⊢ (??(????(???%))?); >Hcurrent
    cases (nth i ?? (None sig)) [|#x] @tape_move_null_action ] ]
qed.

lemma comp_q0_q2_neq :
  ∀i,j,sig,n,v.i < S n → j < S n → 
  (nth i ? (current_chars ?? v) (None ?) ≠ nth j ? (current_chars ?? v) (None ?)) → 
  step sig n (compare_step i j sig n) (mk_mconfig ??? comp0 v) 
  = mk_mconfig ??? comp2 v.
#i #j #sig #n #v #Hi #Hj lapply (refl ? (nth i ?(current_chars ?? v)(None ?)))
cases (nth i ?? (None ?)) in ⊢ (???%→?);
[ #Hnth #_ @comp_q0_q2_null // % //
| #ai #Hai lapply (refl ? (nth j ?(current_chars ?? v)(None ?)))
  cases (nth j ?? (None ?)) in ⊢ (???%→?);
  [ #Hnth #_ @comp_q0_q2_null // %2 //
  | #aj #Haj * #Hneq
    whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
    [ whd in match (trans ????); >Hai >Haj
      whd in ⊢ (??(???%)?); cut ((ai==aj)=false)
      [>(\bf ?) /2 by not_to_not/ % #Haiaj @Hneq
       >Hai >Haj //
      | #Haiaj >Haiaj % ]
    | whd in match (trans ????); >Hai >Haj
      whd in ⊢ (??(????(???%))?); cut ((ai==aj)=false)
      [>(\bf ?) /2 by not_to_not/ % #Haiaj @Hneq
       >Hai >Haj //
      |#Hcut >Hcut @tape_move_null_action
      ]
    ]
  ]
]
qed.

lemma comp_q0_q1 :
  ∀i,j,sig,n,v,a.i ≠ j → i < S n → j < S n → 
  nth i ? (current_chars ?? v) (None ?) = Some ? a →
  nth j ? (current_chars ?? v) (None ?) = Some ? a → 
  step sig n (compare_step i j sig n) (mk_mconfig ??? comp0 v) =
    mk_mconfig ??? comp1 
     (change_vec ? (S n) 
       (change_vec ?? v
         (tape_move_right ? (nth i ? v (niltape ?))) i)
       (tape_move_right ? (nth j ? v (niltape ?))) j).
#i #j #sig #n #v #a #Heq #Hi #Hj #Ha1 #Ha2
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
[ whd in match (trans ????);
  >Ha1 >Ha2 whd in ⊢ (??(???%)?); >(\b ?) //
| whd in match (trans ????);
  >Ha1 >Ha2 whd in ⊢ (??(????(???%))?); >(\b ?) //
  change with (change_vec ?????) in ⊢ (??(????%)?);
  <(change_vec_same … v j (niltape ?)) in ⊢ (??%?);
  <(change_vec_same … v i (niltape ?)) in ⊢ (??%?);
  >tape_move_multi_def 
  >pmap_change >pmap_change <tape_move_multi_def
  >tape_move_null_action
  @eq_f2 // >nth_change_vec_neq //
]
qed.

lemma sem_comp_step :
  ∀i,j,sig,n.i ≠ j → i < S n → j < S n → 
  compare_step i j sig n ⊨ 
    [ comp1: R_comp_step_true i j sig n, 
             R_comp_step_false i j sig n ].
#i #j #sig #n #Hneq #Hi #Hj #int
lapply (refl ? (current ? (nth i ? int (niltape ?))))
cases (current ? (nth i ? int (niltape ?))) in ⊢ (???%→?);
[ #Hcuri %{2} %
  [| % [ %
    [ whd in ⊢ (??%?); >comp_q0_q2_null /2/ 
    | normalize in ⊢ (%→?); #H destruct (H) ]
  | #_ % // % %2 // ] ]
| #a #Ha lapply (refl ? (current ? (nth j ? int (niltape ?))))
  cases (current ? (nth j ? int (niltape ?))) in ⊢ (???%→?);
  [ #Hcurj %{2} %
    [| % [ %
       [ whd in ⊢ (??%?); >comp_q0_q2_null /2/ %2
       | normalize in ⊢ (%→?); #H destruct (H) ]
       | #_ % // >Ha >Hcurj % % % #H destruct (H) ] ]
  | #b #Hb %{2} cases (true_or_false (a == b)) #Hab
    [ %
      [| % [ % 
        [whd in ⊢  (??%?);  >(comp_q0_q1 … a Hneq Hi Hj) //
         >(\P Hab) <Hb @sym_eq @nth_vec_map
        | #_ whd >(\P Hab) %{b} % // % // <(\P Hab) // ]
        | * #H @False_ind @H %
      ] ]
    | %
      [| % [ % 
        [whd in ⊢  (??%?);  >comp_q0_q2_neq //
         <(nth_vec_map ?? (current …) i ? int (niltape ?))
         <(nth_vec_map ?? (current …) j ? int (niltape ?)) >Ha >Hb
         @(not_to_not ??? (\Pf Hab)) #H destruct (H) %
        | normalize in ⊢ (%→?); #H destruct (H) ]
      | #_ % // % % >Ha >Hb @(not_to_not ??? (\Pf Hab)) #H destruct (H) % ] ]
    ]
  ]
]
qed.
(* copy a character from src tape to dst tape without moving them *)

definition copy_states ≝ initN 3.

definition cc0 : copy_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition cc1 : copy_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).

definition trans_copy_char_N ≝ 
 λsrc,dst.λsig:FinSet.λn.
 λp:copy_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 match pi1 … q with
 [ O ⇒ 〈cc1,change_vec ? (S n) 
           (change_vec ? (S n) (null_action ? n) (〈None ?,N〉) src)
           (〈nth src ? a (None ?),N〉) dst〉
 | S _ ⇒ 〈cc1,null_action ? n〉 ].

definition copy_char_N ≝ 
  λsrc,dst,sig,n.
  mk_mTM sig n copy_states (trans_copy_char_N src dst sig n) 
    cc0 (λq.q == cc1).

definition R_copy_char_N ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  outt = change_vec ?? int
          (tape_write  ? (nth dst ? int (niltape ?))
            (current ? (nth src ? int (niltape ?)))) dst.

lemma copy_char_N_q0_q1 :
  ∀src,dst,sig,n,v.src ≠ dst → src < S n → dst < S n → 
  step sig n (copy_char_N src dst sig n) (mk_mconfig ??? cc0 v) =
    mk_mconfig ??? cc1 
     (change_vec ?? v
       (tape_write  ? (nth dst ? v (niltape ?))
          (current ? (nth src ? v (niltape ?)))) dst).
#src #dst #sig #n #v #Heq #Hsrc #Hdst
whd in ⊢ (??%?); @eq_f
<(change_vec_same … v dst (niltape ?)) in ⊢ (??%?);
<(change_vec_same … v src (niltape ?)) in ⊢ (??%?);
>tape_move_multi_def
>pmap_change >pmap_change <tape_move_multi_def
>tape_move_null_action @eq_f3 //
[ >change_vec_same %
| >change_vec_same >change_vec_same >nth_current_chars // ]
qed.

lemma sem_copy_char_N:
  ∀src,dst,sig,n.src ≠ dst → src < S n → dst < S n → 
  copy_char_N src dst sig n ⊨ R_copy_char_N src dst sig n.
#src #dst #sig #n #Hneq #Hsrc #Hdst #int
%{2} % [| % [ % | whd >copy_char_N_q0_q1 // ]]
qed.

(* copy a character from src tape to dst tape and advance both tape to
   the right - useful for copying stings 

definition copy_char_states ≝ initN 3.

definition trans_copy_char ≝ 
 λsrc,dst.λsig:FinSet.λn.
 λp:copy_char_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 match pi1 … q with
 [ O ⇒ 〈cc1,change_vec ? (S n) 
           (change_vec ? (S n) (null_action ? n) (〈None ?,R〉) src)
           (〈nth src ? a (None ?),R〉) dst〉
 | S _ ⇒ 〈cc1,null_action ? n〉 ].

definition copy_char ≝ 
  λsrc,dst,sig,n.
  mk_mTM sig n copy_char_states (trans_copy_char src dst sig n) 
    cc0 (λq.q == cc1).

definition R_copy_char ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  outt = change_vec ?? 
         (change_vec ?? int
          (tape_move_mono ? (nth src ? int (niltape ?)) 〈None ?, R〉) src)
          (tape_move_mono ? (nth dst ? int (niltape ?)) 
           〈current ? (nth src ? int (niltape ?)), R〉) dst.

lemma copy_char_q0_q1 :
  ∀src,dst,sig,n,v.src ≠ dst → src < S n → dst < S n → 
  step sig n (copy_char src dst sig n) (mk_mconfig ??? cc0 v) =
    mk_mconfig ??? cc1 
     (change_vec ? (S n) 
       (change_vec ?? v
         (tape_move_mono ? (nth src ? v (niltape ?)) 〈None ?, R〉) src)
            (tape_move_mono ? (nth dst ? v (niltape ?)) 〈current ? (nth src ? v (niltape ?)), R〉) dst).
#src #dst #sig #n #v #Heq #Hsrc #Hdst
whd in ⊢ (??%?);
<(change_vec_same … v dst (niltape ?)) in ⊢ (??%?);
<(change_vec_same … v src (niltape ?)) in ⊢ (??%?);
>tape_move_multi_def @eq_f2 //
>pmap_change >pmap_change <tape_move_multi_def
>tape_move_null_action @eq_f2 // @eq_f2
[ >change_vec_same %
| >change_vec_same >change_vec_same // ]
qed.

lemma sem_copy_char:
  ∀src,dst,sig,n.src ≠ dst → src < S n → dst < S n → 
  copy_char src dst sig n ⊨ R_copy_char src dst sig n.
#src #dst #sig #n #Hneq #Hsrc #Hdst #int
%{2} % [| % [ % | whd >copy_char_q0_q1 // ]]
qed.*)

definition copy0 : copy_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition copy1 : copy_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition copy2 : copy_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).

definition trans_copy_step ≝ 
 λsrc,dst.λsig:FinSet.λn.
 λp:copy_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 match pi1 … q with
 [ O ⇒ match nth src ? a (None ?) with
   [ None ⇒ 〈copy2,null_action sig n〉
   | Some ai ⇒ match nth dst ? a (None ?) with 
     [ None ⇒ 〈copy2,null_action ? n〉
     | Some aj ⇒ 
         〈copy1,change_vec ? (S n) 
           (change_vec ? (S n) (null_action ? n) (〈None ?,R〉) src)
           (〈Some ? ai,R〉) dst〉
     ]
   ]
 | S q ⇒ match q with 
   [ O ⇒ (* 1 *) 〈copy1,null_action ? n〉
   | S _ ⇒ (* 2 *) 〈copy2,null_action ? n〉 ] ].

definition copy_step ≝ 
  λsrc,dst,sig,n.
  mk_mTM sig n copy_states (trans_copy_step src dst sig n) 
    copy0 (λq.q == copy1 ∨ q == copy2).

definition R_copy_step_true ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  ∃x,y.
   current ? (nth src ? int (niltape ?)) = Some ? x ∧
   current ? (nth dst ? int (niltape ?)) = Some ? y ∧
   outt = change_vec ?? 
            (change_vec ?? int
              (tape_move_mono ? (nth src ? int (niltape ?)) 〈None ?, R〉) src)
            (tape_move_mono ? (nth dst ? int (niltape ?)) 〈Some ? x, R〉) dst.

definition R_copy_step_false ≝ 
  λsrc,dst:nat.λsig,n.λint,outt: Vector (tape sig) (S n).
    (current ? (nth src ? int (niltape ?)) = None ? ∨
     current ? (nth dst ? int (niltape ?)) = None ?) ∧ outt = int.

lemma copy_q0_q2_null :
  ∀src,dst,sig,n,v.src < S n → dst < S n → 
  (nth src ? (current_chars ?? v) (None ?) = None ? ∨
   nth dst ? (current_chars ?? v) (None ?) = None ?) → 
  step sig n (copy_step src dst sig n) (mk_mconfig ??? copy0 v) 
  = mk_mconfig ??? copy2 v.
#src #dst #sig #n #v #Hi #Hj
whd in ⊢ (? → ??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (?→??%?);
* #Hcurrent
[ @eq_f2
  [ whd in ⊢ (??(???%)?); >Hcurrent %
  | whd in ⊢ (??(????(???%))?); >Hcurrent @tape_move_null_action ]
| @eq_f2
  [ whd in ⊢ (??(???%)?); >Hcurrent cases (nth src ?? (None sig)) //
  | whd in ⊢ (??(????(???%))?); >Hcurrent
    cases (nth src ?? (None sig)) [|#x] @tape_move_null_action ] ]
qed.

lemma copy_q0_q1 :
  ∀src,dst,sig,n,v,a,b.src ≠ dst → src < S n → dst < S n → 
  nth src ? (current_chars ?? v) (None ?) = Some ? a →
  nth dst ? (current_chars ?? v) (None ?) = Some ? b → 
  step sig n (copy_step src dst sig n) (mk_mconfig ??? copy0 v) =
    mk_mconfig ??? copy1 
     (change_vec ? (S n) 
       (change_vec ?? v
         (tape_move_mono ? (nth src ? v (niltape ?)) 〈None ?, R〉) src)
            (tape_move_mono ? (nth dst ? v (niltape ?)) 〈Some ? a, R〉) dst).
#src #dst #sig #n #v #a #b #Heq #Hsrc #Hdst #Ha1 #Ha2
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
[ whd in match (trans ????);
  >Ha1 >Ha2 whd in ⊢ (??(???%)?); >(\b ?) //
| whd in match (trans ????);
  >Ha1 >Ha2 whd in ⊢ (??(????(???%))?); >(\b ?) //
  change with (change_vec ?????) in ⊢ (??(????%)?);
  <(change_vec_same … v dst (niltape ?)) in ⊢ (??%?);
  <(change_vec_same … v src (niltape ?)) in ⊢ (??%?);
  >tape_move_multi_def 
  >pmap_change >pmap_change <tape_move_multi_def
  >tape_move_null_action
  @eq_f2 // >nth_change_vec_neq //
]
qed.

lemma sem_copy_step :
  ∀src,dst,sig,n.src ≠ dst → src < S n → dst < S n → 
  copy_step src dst sig n ⊨ 
    [ copy1: R_copy_step_true src dst sig n, 
            R_copy_step_false src dst sig n ].
#src #dst #sig #n #Hneq #Hsrc #Hdst #int
lapply (refl ? (current ? (nth src ? int (niltape ?))))
cases (current ? (nth src ? int (niltape ?))) in ⊢ (???%→?);
[ #Hcur_src %{2} %
  [| % [ %
    [ whd in ⊢ (??%?); >copy_q0_q2_null /2/ 
    | normalize in ⊢ (%→?); #H destruct (H) ]
  | #_ % // % // ] ]
| #a #Ha lapply (refl ? (current ? (nth dst ? int (niltape ?))))
  cases (current ? (nth dst ? int (niltape ?))) in ⊢ (???%→?);
  [ #Hcur_dst %{2} %
    [| % [ %
       [ whd in ⊢ (??%?); >copy_q0_q2_null /2/ 
       | normalize in ⊢ (%→?); #H destruct (H) ]
       | #_ % // %2 >Hcur_dst % ] ]
  | #b #Hb %{2} %
    [| % [ % 
      [whd in ⊢  (??%?);  >(copy_q0_q1 … a b Hneq Hsrc Hdst) //
      | #_ %{a} %{b} % // % //]
      | * #H @False_ind @H %
      ]
    ]
  ]
]
qed.


(* advance in parallel on tapes src and dst; stops if one of the
   two tapes is in oveflow *)

definition parmove_states ≝ initN 3.

definition parmove0 : parmove_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition parmove1 : parmove_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition parmove2 : parmove_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).

(*
   src: a b c ... z ---→ a b c ... z 
        ^                            ^
   dst: _ _ _ ... _ ---→ a b c ... z 
        ^                            ^

   0) (x,_) → (x,_)(R,R) → 1
      (None,_) → None 2
   1) (_,_) → None 1
   2) (_,_) → None 2
*)

definition trans_parmove_step ≝ 
 λsrc,dst,sig,n,D.
 λp:parmove_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 match pi1 … q with
 [ O ⇒ match nth src ? a (None ?) with
   [ None ⇒ 〈parmove2,null_action sig n〉
   | Some a0 ⇒ match nth dst ? a (None ?) with
     [ None ⇒ 〈parmove2,null_action ? n〉
     | Some a1 ⇒ 〈parmove1,change_vec ? (S n)
                          (change_vec ?(S n)
                           (null_action ? n) (〈None ?,D〉) src)
                          (〈None ?,D〉) dst〉 ] ]
 | S q ⇒ match q with 
   [ O ⇒ (* 1 *) 〈parmove1,null_action ? n〉
   | S _ ⇒ (* 2 *) 〈parmove2,null_action ? n〉 ] ].

definition parmove_step ≝ 
  λsrc,dst,sig,n,D.
  mk_mTM sig n parmove_states (trans_parmove_step src dst sig n D) 
    parmove0 (λq.q == parmove1 ∨ q == parmove2).

definition R_parmove_step_true ≝ 
  λsrc,dst,sig,n,D.λint,outt: Vector (tape sig) (S n).
  ∃x1,x2.
   current ? (nth src ? int (niltape ?)) = Some ? x1 ∧
   current ? (nth dst ? int (niltape ?)) = Some ? x2 ∧
   outt = change_vec ?? 
            (change_vec ?? int
              (tape_move ? (nth src ? int (niltape ?)) D) src)
            (tape_move ? (nth dst ? int (niltape ?)) D) dst.

definition R_parmove_step_false ≝ 
  λsrc,dst:nat.λsig,n.λint,outt: Vector (tape sig) (S n).
  (current ? (nth src ? int (niltape ?)) = None ?  ∨
   current ? (nth dst ? int (niltape ?)) = None ?) ∧
   outt = int.

lemma parmove_q0_q2_null_src :
  ∀src,dst,sig,n,D,v.src < S n → dst < S n → 
  nth src ? (current_chars ?? v) (None ?) = None ? → 
  step sig n (parmove_step src dst sig n D)
    (mk_mconfig ??? parmove0 v) =
    mk_mconfig ??? parmove2 v.
#src #dst #sig #n #D #v #Hsrc #Hdst #Hcurrent
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?);
@eq_f2
[ whd in ⊢ (??(???%)?); >Hcurrent %
| whd in ⊢ (??(????(???%))?); >Hcurrent @tape_move_null_action ]
qed.

lemma parmove_q0_q2_null_dst :
  ∀src,dst,sig,n,D,v,s.src < S n → dst < S n → 
  nth src ? (current_chars ?? v) (None ?) = Some ? s → 
  nth dst ? (current_chars ?? v) (None ?) = None ? → 
  step sig n (parmove_step src dst sig n D)
    (mk_mconfig ??? parmove0 v) =
    mk_mconfig ??? parmove2 v.
#src #dst #sig #n #D #v #s #Hsrc #Hdst #Hcursrc #Hcurdst
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?);
@eq_f2
[ whd in ⊢ (??(???%)?); >Hcursrc whd in ⊢ (??(???%)?); >Hcurdst %
| whd in ⊢ (??(????(???%))?); >Hcursrc
  whd in ⊢ (??(????(???%))?); >Hcurdst @tape_move_null_action ]
qed.

lemma parmove_q0_q1 :
  ∀src,dst,sig,n,D,v.src ≠ dst → src < S n → dst < S n → 
  ∀a1,a2.
  nth src ? (current_chars ?? v) (None ?) = Some ? a1 →
  nth dst ? (current_chars ?? v) (None ?) = Some ? a2 → 
  step sig n (parmove_step src dst sig n D)
    (mk_mconfig ??? parmove0 v) =
    mk_mconfig ??? parmove1 
     (change_vec ? (S n) 
       (change_vec ?? v
         (tape_move ? (nth src ? v (niltape ?)) D) src)
       (tape_move ? (nth dst ? v (niltape ?)) D) dst).
#src #dst #sig #n #D #v #Hneq #Hsrc #Hdst
#a1 #a2 #Hcursrc #Hcurdst
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
[ whd in match (trans ????);
  >Hcursrc >Hcurdst %
| whd in match (trans ????);
  >Hcursrc >Hcurdst whd in ⊢ (??(????(???%))?); 
  >tape_move_multi_def <(change_vec_same ?? v dst (niltape ?)) in ⊢ (??%?);
  >pmap_change <(change_vec_same ?? v src (niltape ?)) in ⊢(??%?);
  >pmap_change <tape_move_multi_def >tape_move_null_action
  @eq_f2 // >nth_change_vec_neq //
]
qed.

lemma sem_parmove_step :
  ∀src,dst,sig,n,D.src ≠ dst → src < S n → dst < S n → 
  parmove_step src dst sig n D ⊨ 
    [ parmove1: R_parmove_step_true src dst sig n D, 
             R_parmove_step_false src dst sig n ].
#src #dst #sig #n #D #Hneq #Hsrc #Hdst #int
lapply (refl ? (current ? (nth src ? int (niltape ?))))
cases (current ? (nth src ? int (niltape ?))) in ⊢ (???%→?);
[ #Hcursrc %{2} %
  [| % [ %
    [ whd in ⊢ (??%?); >parmove_q0_q2_null_src /2/
    | normalize in ⊢ (%→?); #H destruct (H) ]
    | #_ % // % // ] ]
| #a #Ha lapply (refl ? (current ? (nth dst ? int (niltape ?))))
  cases (current ? (nth dst ? int (niltape ?))) in ⊢ (???%→?);
  [ #Hcurdst %{2} %
    [| % [ %
      [ whd in ⊢ (??%?); >(parmove_q0_q2_null_dst …) /2/ 
      | normalize in ⊢ (%→?); #H destruct (H) ]
      | #_ % // %2 // ] ]
  | #b #Hb %{2} %
    [| % [ % 
      [whd in ⊢  (??%?); >(parmove_q0_q1 … Hneq Hsrc Hdst ? b ??)
        [2: <(nth_vec_map ?? (current …) dst ? int (niltape ?)) //
        |3: <(nth_vec_map ?? (current …) src ? int (niltape ?)) //
        | // ]
      | #_ %{a} %{b} % // % // ]
      | * #H @False_ind @H % ]
]]]
qed.

(* perform a symultaneous test on all tapes; ends up in state partest1 if
   the test is succesfull and partest2 otherwise *)

definition partest_states ≝ initN 3.

definition partest0 : partest_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition partest1 : partest_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition partest2 : partest_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).

definition trans_partest ≝ 
 λsig,n,test.
 λp:partest_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 if test a then 〈partest1,null_action sig n〉 
 else 〈partest2,null_action ? n〉.

definition partest ≝ 
  λsig,n,test.
  mk_mTM sig n partest_states (trans_partest sig n test) 
    partest0 (λq.q == partest1 ∨ q == partest2).

definition R_partest_true ≝ 
  λsig,n,test.λint,outt: Vector (tape sig) (S n).
  test (current_chars ?? int) = true ∧ outt = int.
  
definition R_partest_false ≝ 
  λsig,n,test.λint,outt: Vector (tape sig) (S n).
  test (current_chars ?? int) = false ∧ outt = int.

lemma partest_q0_q1:
  ∀sig,n,test,v.
  test (current_chars ?? v) = true → 
  step sig n (partest sig n test)(mk_mconfig ??? partest0 v) 
    = mk_mconfig ??? partest1 v.
#sig #n #test #v #Htest
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?);
@eq_f2
[ whd in ⊢ (??(???%)?); >Htest %
| whd in ⊢ (??(????(???%))?); >Htest @tape_move_null_action ]
qed.

lemma partest_q0_q2:
  ∀sig,n,test,v.
  test (current_chars ?? v) = false → 
  step sig n (partest sig n test)(mk_mconfig ??? partest0 v) 
    = mk_mconfig ??? partest2 v.
#sig #n #test #v #Htest
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?);
@eq_f2
[ whd in ⊢ (??(???%)?); >Htest %
| whd in ⊢ (??(????(???%))?); >Htest @tape_move_null_action ]
qed.

lemma sem_partest:
  ∀sig,n,test.
  partest sig n test ⊨ 
    [ partest1: R_partest_true sig n test, R_partest_false sig n test ].
#sig #n #test #int
cases (true_or_false (test (current_chars ?? int))) #Htest
[ %{2} %{(mk_mconfig ? partest_states n partest1 int)} %
  [ % [ whd in ⊢ (??%?); >partest_q0_q1 /2/ | #_ % // ] 
  | * #H @False_ind @H %
  ]
| %{2} %{(mk_mconfig ? partest_states n partest2 int)} %
  [ % [ whd in ⊢ (??%?); >partest_q0_q2 /2/ 
      | whd in ⊢ (??%%→?); #H destruct (H)]
  | #_ % //]
]
qed.