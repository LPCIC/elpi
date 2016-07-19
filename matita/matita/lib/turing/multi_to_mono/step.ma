
include "turing/multi_to_mono/exec_moves.ma".

definition Mono_realize ≝ Realize.

definition to_sig ≝ λQ,sig.λc:sig_ext (TA Q sig).
  match c with 
  [None ⇒ None ?
  |Some a ⇒ match a with 
    [inl x ⇒ None ? (* this is not possible *)
    |inr x ⇒ Some ? x]].

definition to_sig_inv ≝ λQ,sig.λc1:(option sig) × move.λc2.
  match (fst ?? c1) with 
  [None ⇒ c2
  |Some a ⇒ Some ? (inr Q ? a)].

definition transf ≝ λQ,sig:FinSet.λn.
 λt: Q × (Vector (option sig) n) → Q × (Vector ((option sig) × move) n).
 λa:MTA (HC Q n) sig (S n).
  let qM ≝ nth n ? (vec … a) (blank ?) in
  let a1 ≝ resize_vec ? (S n) a n (blank ?) in
  let a2 ≝ vec_map ?? (to_sig ? sig) n a1 in
  match qM with 
  [None ⇒ all_blanks (TA (HC Q n) sig) (S n)
  |Some p ⇒ 
    match p with 
    [inl p1 ⇒ 
      let 〈q1,actions〉 ≝ t 〈fst ?? p1, a2〉 in
      let moves ≝ vec_map ?? (snd ??) n actions in 
      let new_chars ≝ pmap_vec ??? (to_sig_inv (HC Q n) ?) n actions a1 in
      vec_cons_right ? (Some ? (inl ?? 〈q1,moves〉)) n new_chars
    |inr p2 ⇒ all_blanks (TA (HC Q n) sig) (S n)]
  ].

lemma transf_eq: ∀Q,sig,n,t.∀a:MTA (HC Q n) sig (S n).
  ∀a1,a2,q,m,q1,actions,moves,new_chars.
  nth n ? (vec … a) (blank ?) = Some ? (inl ?? 〈q,m〉) →
  a1 = resize_vec ? (S n) a n (blank ?) →
  a2 = vec_map ?? (to_sig ? sig) n a1 →
  t 〈q, a2〉 = 〈q1,actions〉 →
  moves = vec_map ?? (snd ??) n actions → 
  new_chars = pmap_vec ??? (to_sig_inv (HC Q n) ?) n actions a1  →
  transf Q sig n t a = 
    vec_cons_right ? (Some ? (inl ?? 〈q1,moves〉)) n new_chars.
#Q #sig #n #t #a #a1 #a2 #q #m #q1 #actions #moves #new_chars
#Hnth #Ha1 #Ha2 #Ht #Hmoves #Hnew_chars
whd in ⊢ (??%?); >Hnth whd in ⊢ (??%?); <Ha1 <Ha2 >Ht
@eq_cons_right [<Hmoves // |<Hnew_chars // ]
qed.
  
lemma transf_eq_ex: ∀Q,sig,n,t.∀a:MTA (HC Q n) sig (S n).
  ∀q,m.nth n ? (vec … a) (blank ?) = Some ? (inl ?? 〈q,m〉)→
  ∃a1.a1 = resize_vec ? (S n) a n (blank ?) ∧
  ∃a2. a2 = vec_map ?? (to_sig ? sig) n a1 ∧
  ∃q1,actions. t 〈q, a2〉 = 〈q1,actions〉 ∧
  ∃moves.moves = vec_map ?? (snd ??) n actions ∧ 
  ∃new_chars.new_chars = pmap_vec ??? (to_sig_inv (HC Q n) ?) n actions a1 ∧
  transf Q sig n t a = 
    vec_cons_right ? (Some ? (inl ?? 〈q1,moves〉)) n new_chars.
#Q #sig #n #t #a #q #m #H 
%{(resize_vec ? (S n) a n (blank ?))} % [%] 
% [2:% [%] | skip] % [2: % [ 2: % [@eq_pair_fst_snd ] |skip] | skip]
% [2:% [%] | skip] % [2:% [%] | skip] whd in ⊢ (??%?); >H whd in ⊢ (??%?);
>(eq_pair_fst_snd … (t …)) % 
qed.

(*
lemma nth_transf: ∀Q,sig,n,t.∀a:MTA (HC Q n) sig (S n).
  ∀a1,a2,q,m,q1,actions,moves.
  nth n ? (vec … a) (blank ?) = Some ? (inl ?? 〈q,m〉) →
  a1 = resize_vec ? (S n) a n (blank ?) →
  a2 = vec_map ?? (to_sig ? sig) n a1 →
  t 〈q, a2〉 = 〈q1,actions〉 →
  moves = vec_map ?? (snd ??) n actions → 
  nth n ? (vec … (transf Q sig n t a)) (blank ?) = Some ? (inl ?? 〈q1,moves〉).
#Q #sig #n #t #a #a1 #a2 #q #m #q1 #actions #moves
#Hnth #Ha1 #Ha2 #Ht #Hmoves
*)

(*********************************** stepM ************************************)
definition optf ≝ λA,B:Type[0].λf:A →B.λd,oa.
  match oa with 
  [ None ⇒ d
  | Some a ⇒ f a ].

lemma optf_Some : ∀A,B,f,a,d. optf A B f d (Some A a) = f a.
// qed.

definition stepM ≝ λQ,sig,n,trans.
  writef ? (optf ?? (transf Q sig (S n) trans) (all_blanks …)) ·
  exec_moves Q sig (S n) (S n).

let rec to_sig_map Q sig l on l ≝
  match l with 
  [ nil ⇒ nil ?
  | cons a tl ⇒ match to_sig Q sig a with 
    [ None ⇒ nil ?
    | Some c ⇒ c::(to_sig_map Q sig tl)]].


definition to_sig_tape ≝ λQ,sig,t.
  match t with
  [ niltape  ⇒ niltape ?
  | leftof a l ⇒ match to_sig Q sig a with 
    [ None ⇒ niltape ?
    | Some x ⇒ leftof ? x (to_sig_map Q sig l) ]
  | rightof a l ⇒ match to_sig Q sig a with 
    [ None ⇒ niltape ?
    | Some x ⇒ rightof ? x (to_sig_map Q sig l) ]
  | midtape ls a rs ⇒ match to_sig Q sig a with 
    [ None ⇒ niltape ?
    | Some x ⇒ midtape ? (to_sig_map Q sig ls) x (to_sig_map Q sig rs) ]
  ].

let rec rb_tapes Q sig n ls (a:MTA Q sig (S n)) rs i on i ≝
  match i with 
  [ O ⇒ mk_Vector ? 0 (nil ?) (refl ??)
  | S j ⇒ vec_cons_right ? (to_sig_tape ?? (rb_trace_i ? (S n) ls (vec … a) rs j)) j
           (rb_tapes Q sig n ls a rs j)].
 
lemma nth_rb_tapes : ∀Q,sig,n,ls.∀a:MTA Q sig (S n).∀rs,j,i. i < j →
  nth i ? (rb_tapes Q sig n ls (a:MTA Q sig (S n)) rs j) (niltape ?) =
    to_sig_tape ?? (rb_trace_i ? (S n) ls (vec … a) rs i).
#Q #sig #n #ls #a #rs #j elim j
  [#i #H @False_ind /2/
  |#k #Hind #i #lti cases (le_to_or_lt_eq … (le_S_S_to_le … lti))
    [#Hlt >nth_cons_right_lt [@Hind //|//]
    |#Heq >Heq @nth_cons_right_n
    ]
  ]
qed.
  
 
(* q0 is a default value *)
definition get_state ≝ λQ,sig,n.λa:MTA (HC Q n) sig (S n).λq0.
  match nth n ? (vec … a) (blank ?) with 
  [ None ⇒ q0 (* impossible *)
  | Some qM ⇒ match qM with
    [inl qM1 ⇒ fst ?? qM1 
    |inr _ ⇒ q0 (* impossible *) ]].
    
definition get_chars ≝ λQ,sig,n.λa:MTA (HC Q n) sig (S n).
  let a1 ≝ resize_vec ? (S n) a n (blank ?) in
  vec_map ?? (to_sig ? sig) n a1.
  
lemma get_chars_def : ∀Q,sig,n.∀a:MTA (HC Q n) sig (S n).
  get_chars … a =
    vec_map ?? (to_sig ? sig) n (resize_vec ? (S n) a n (blank ?)).
// qed. 

include "turing/turing.ma".

definition readback_config ≝
  λQ,sig,n,q0,ls.λa:MTA (HC Q (S n)) sig (S (S n)).λrs.
  mk_mconfig sig Q n 
    (get_state Q sig (S n) a q0)
    (rb_tapes (HC Q (S n)) sig (S n) ls a rs (S n)).

lemma state_readback : ∀Q,sig,n,q0,ls,a,rs.
  cstate … (readback_config Q sig n q0 ls a rs) =
    get_state Q sig (S n) a q0.
// qed.

lemma tapes_readback : ∀Q,sig,n,q0,ls,a,rs.
  ctapes … (readback_config Q sig n q0 ls a rs) =
    rb_tapes (HC Q (S n)) sig (S n) ls a rs (S n).
// qed.
    
definition R_stepM ≝ λsig.λn.λM:mTM sig n.λt1,t2.
∀a,ls,rs. 
  t1 = midtape ? ls a rs → 
  (∀i.regular_trace (TA (HC (states … M) (S n)) sig) (S(S n)) a ls rs i) → 
  is_head ?? (nth (S n) ? (vec … a) (blank ?)) = true →  
  no_head_in … ls →
  no_head_in … rs →
  ∃ls1,a1,rs1. 
   t2 = midtape (MTA (HC (states … M) (S n)) sig (S(S n))) ls1 a1 rs1 ∧
   (∀i.regular_trace (TA (HC (states … M) (S n)) sig) (S(S n)) a1 ls1 rs1 i) ∧
   readback_config ? sig n (start … M) ls1 a1 rs1 =
     step sig n M (readback_config ? sig n (start … M) ls a rs).

lemma nth_vec_map_lt : 
  ∀A,B,f,i,n.∀v:Vector A n.∀d1,d2.i < n →
  nth i ? (vec_map A B f n v) d1 = f (nth i ? v d2).
#A #B #f #i #n #v #d1 #d2 #ltin >(nth_default B i n ? d1 (f d2) ltin) @sym_eq @nth_vec_map 
qed.

lemma ctapes_mk_config : ∀sig,Q,n,s,t.
  ctapes sig Q n (mk_mconfig sig Q n s t) = t.
// qed.

lemma cstate_rb: ∀sig,n.∀M:mTM sig n.∀ls,a,rs.∀q,m.
  nth (S n) ? (vec … a) (blank ?) = Some ? (inl ?? 〈q,m〉) →
  cstate sig (states sig n M) n
      (readback_config (states sig n M) sig n (start sig n M) ls a rs) = q.
#sig #n #M #ls #a #rs #q #m #H
>state_readback whd in ⊢ (??%?); >H %
qed.

axiom eq_cstate_get_state: ∀sig,n.∀M:mTM sig n.∀ls,a,rs.
  is_head ?? (nth (S n) ? (vec … a) (blank ?)) = true →
  cstate sig (states sig n M) n
      (readback_config (states sig n M) sig n (start sig n M) ls a rs) = 
  get_state (states sig n M) sig (S n) a (start sig n M). 

axiom eq_current_chars_resize: ∀sig,n.∀M:mTM sig n.∀ls,a,rs.
  current_chars sig n
   (ctapes sig (states sig n M) n
    (readback_config (states sig n M) sig n (start sig n M) ls a rs)) =
  get_chars … a.
  
(*
lemma rb_trans : ∀sig,Q,n.∀M:mTM sig n.∀ls,a,rs,q,m.
  nth (S n) ? (vec … a) (blank ?) = Some ? (inl ?? 〈q,m〉) →
  transf (states sig n M) sig (S n) (trans sig n M) a =
  trans sig n M 〈q,get_chars … a〉.
*)

lemma nth_pmap_lt :
  ∀A,B,C,f,i,n.∀v1:Vector A n.∀v2:Vector B n.∀d1,d2,d3.i < n→
  f (nth i ? v1 d1) (nth i ? v2 d2) = nth i ? (pmap_vec A B C f n v1 v2) d3.
#A #B #C #f #i elim i
[ *
  [ #v1 #v2 #d1 #d2 #d3 #Hlt @False_ind /2/  
  | #n0 #v1 #v2 #d1 #d2 #d3 #_ >(vec_expand … v1)
    >(vec_expand … v2) >(nth_default … d3 (f d1 d2)) [% | // ]]
| #i0 #IH *
  [ #v1 #v2 #d1 #d2 #d3 #Hlt @False_ind /2/  
  | #n #v1 #v2 #d1 #d2 #d3 #Hlt>(vec_expand … v1) 
     >(vec_expand … v2) 
     whd in match (nth …d1); whd in match (tail ??); 
     whd in match (nth … d2); whd in match (tail B ?);
     whd in match (nth … d3); whd in match (tail C ?); 
     <(IH n ?? d1 d2 d3) [2:@le_S_S_to_le @Hlt] %
  ] ]
qed.

lemma tape_move_mono_def : ∀sig,t,a,m.
  tape_move_mono sig t 〈a,m〉 = tape_move sig (tape_write sig t a) m.
// qed.

axiom to_sig_move : ∀Q,sig,n,t,m.
  to_sig_tape (HC Q (S n)) sig
  (tape_move (sig_ext (TA (HC Q (S n)) sig)) t m)
  = tape_move sig (to_sig_tape ?? t) m.
  
definition to_sig_conv :∀Q,sig:FinSet.∀n.
 option sig → option (sig_ext (TA (HC Q (S n)) sig))
≝ λQ,sig,n,c.
  match c with 
  [None ⇒ None ?
  |Some a ⇒ Some ? (Some ? (inr (HC Q (S n)) ? a))].
 
axiom to_sig_write : ∀Q,sig,n,t,c.
  to_sig_tape (HC Q (S n)) sig
  (tape_write ? t (to_sig_conv ??? c))
   = tape_write sig (to_sig_tape ?? t) c.

definition opt ≝ λA.λoc1: option A.λc2.
  match oc1 with [None ⇒ c2 | Some c1 ⇒ c1].

axiom rb_write: ∀sig,n,ls,a,rs,i,c1,c2.
  nth i ? c1 (None ?) = opt ? c2 (nth i ? c1 (None ?)) → 
  rb_trace_i ? n ls c1 rs i =
  tape_write ? (rb_trace_i sig n ls a rs i) c2.
   
lemma sem_stepM : ∀sig,n.∀M:mTM sig n.
  stepM (states sig n M) sig n (trans sig n M) ⊨
    R_stepM sig n M.
#sig #n #M 
@(sem_seq_app … (sem_writef … ) (sem_exec_moves … (le_n ?)))
#tin #tout * #t1 * whd in ⊢ (%→?); #Hwrite #Hmoves 
#a #ls #rs #Htin #H1 #H2 #H3 #H4 >Htin in Hwrite; #Hwrite
lapply (Hwrite … (refl …)) -Hwrite whd in match (right ??); whd in match (left ??);
>optf_Some #Ht1
cut (∃q,m. nth (S n) ? (vec … a) (blank ?) = Some ? (inl ?? 〈q,m〉))
    [lapply H2 cases (nth (S n) ? (vec … a) (blank ?)) 
      [whd in ⊢ (??%?→?); #H destruct (H)
      |* #x whd in ⊢ (??%?→?); #H destruct (H) cases x #q #m %{q} %{m} %
      ]
    ] * #q * #m #HaSn
(* 
lapply (transf_eq … HaSn (refl ??) (refl ??) (eq_pair_fst_snd …) (refl ??) (refl ??))
*)
lapply (Hmoves … Ht1 ?? H3 H4)
  [>(transf_eq … HaSn (refl ??) (refl ??) (eq_pair_fst_snd …) (refl ??) (refl ??))
   >nth_cons_right_n %
  | (* regularity is preserved *) @daemon
  |* #ls1 * #a1 * #rs1 * * * #Htout #Hreg #Hrb #HtrSn
   lapply (HtrSn (S n) (le_n ?) (le_n ?)) -HtrSn #HtrSn
   cut (nth (S n) ? (vec … a1) (blank ?) = 
        nth (S n ) ? (vec … (transf (states sig n M) sig (S n) (trans sig n M) a)) (blank ?))
    [@daemon (* from HtrSn *)] #Ha1
   %{ls1} %{a1} %{rs1} 
   %[%[@Htout |@Hreg]
    |(* commutation *)
     lapply(transf_eq_ex …  (trans sig n M) … HaSn)
     * #c1 * #Hc1 * #c2 * #Hc2 * #q1 * #actions *
     #Htrans * #moves * #Hmoves * #new_chars * #Hnew_chars #Htransf
     @mconfig_eq 
      [(* state *) >state_readback whd in match (step ????);
       >(cstate_rb … HaSn) >eq_current_chars_resize >get_chars_def
       <Hc1 <Hc2 >Htrans whd in ⊢ (???%);
       whd in ⊢ (??%?); >Ha1 >HaSn >Htransf >nth_cons_right_n %
      |>tapes_readback whd in match (step ????);
       >(cstate_rb … HaSn) >eq_current_chars_resize >get_chars_def
       <Hc1 <Hc2 >Htrans >ctapes_mk_config 
       @(eq_vec … (niltape ?)) #i #lti
       >nth_rb_tapes [2:@lti]
       >Hrb [2:@lt_to_le @lti|3:@lti]
       >Htransf whd in match (get_move ?????); (* whd in match (vec_moves ?????); *)
       >get_moves_cons_right 
       (* lhs *)
       <nth_pmap_lt [2:@lti|3:%[@None|@N]|4:@niltape]
       >ctapes_mk_config >nth_rb_tapes [2:@lti]
       (* >nth_vec_map_lt [2:@lti |3:@niltape] *)
       >(eq_pair_fst_snd … (nth i ? actions ?)) 
       >tape_move_mono_def
       cut (snd ?? (nth i ? actions 〈None sig,N〉) = nth i ? moves N)
         [>Hmoves @nth_vec_map] #Hmoves1 >Hmoves1
       >to_sig_move @eq_f2 [2://]
       <to_sig_write @eq_f @rb_write 
       >nth_cons_right_lt [2:@lti]
       >Hnew_chars <nth_pmap_lt [2:@lti|3:@None |4:%[@None|@N]]
       whd in ⊢ (??%%); 
       inversion (\fst  (nth i ? actions 〈None sig,N〉))  
        [#Hcase whd in ⊢ (??%%); >Hcase % |#c #Hcase % ]
      ]
    ]
  ]
qed.
       
       
  
  
  
  










