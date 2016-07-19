include "turing/mono.ma".
include "basics/vectors.ma".

(* We do not distinuish an input tape *)

(* tapes_no = number of ADDITIONAL working tapes *)

record mTM (sig:FinSet) (tapes_no:nat) : Type[1] ≝ 
{ states : FinSet;
  trans : states × (Vector (option sig) (S tapes_no)) → 
    states  × (Vector ((option sig) × move) (S tapes_no));
  start: states;
  halt : states → bool
}.

record mconfig (sig,states:FinSet) (n:nat): Type[0] ≝
{ cstate : states;
  ctapes : Vector (tape sig) (S n)
}.

lemma mconfig_expand: ∀sig,n,Q,c. 
  c = mk_mconfig sig Q n (cstate ??? c) (ctapes ??? c).
#sig #n #Q * // 
qed.
  
lemma mconfig_eq : ∀sig,n,M,c1,c2.
  cstate sig n M c1 = cstate sig n M c2 → 
    ctapes sig n M c1 = ctapes sig n M c2 →  c1 = c2.
#sig #n #M1 * #s1 #t1 * #s2 #t2 //
qed.

definition current_chars ≝ λsig.λn.λtapes.
  vec_map ?? (current sig) (S n) tapes.

lemma nth_current_chars : ∀sig,n,tapes,i.
  nth i ? (current_chars sig n tapes) (None ?) 
   = current sig (nth i ? tapes (niltape sig)).
#sig #n #tapes #i >(nth_vec_map … (current sig) i (S n)) %
qed.

definition tape_move_multi ≝ 
  λsig,n,ts,mvs.
  pmap_vec ??? (tape_move_mono sig) n ts mvs.
  
lemma tape_move_multi_def : ∀sig,n,ts,mvs.
  tape_move_multi sig n ts mvs = pmap_vec ??? (tape_move_mono sig) n ts mvs.
// qed.

definition step ≝ λsig.λn.λM:mTM sig n.λc:mconfig sig (states ?? M) n.
  let 〈news,mvs〉 ≝ trans sig n M 〈cstate ??? c,current_chars ?? (ctapes ??? c)〉 in
  mk_mconfig ??? news (tape_move_multi sig ? (ctapes ??? c) mvs).

definition empty_tapes ≝ λsig.λn.
mk_Vector ? n (make_list (tape sig) (niltape sig) n) ?.
elim n // normalize //
qed.

(************************** Realizability *************************************)
definition loopM ≝ λsig,n.λM:mTM sig n.λi,cin.
  loop ? i (step sig n M) (λc.halt sig n M (cstate ??? c)) cin.

lemma loopM_unfold : ∀sig,n,M,i,cin.
  loopM sig n M i cin = loop ? i (step sig n M) (λc.halt sig n M (cstate ??? c)) cin.
// qed.

definition initc ≝ λsig,n.λM:mTM sig n.λtapes.
  mk_mconfig sig (states sig n M) n (start sig n M) tapes.

definition Realize ≝ λsig,n.λM:mTM sig n.λR:relation (Vector (tape sig) ?).
∀t.∃i.∃outc.
  loopM sig n M i (initc sig n M t) = Some ? outc ∧ R t (ctapes ??? outc).

definition WRealize ≝ λsig,n.λM:mTM sig n.λR:relation (Vector (tape sig) ?).
∀t,i,outc.
  loopM sig n M i (initc sig n M t) = Some ? outc → R t (ctapes ??? outc).

definition Terminate ≝ λsig,n.λM:mTM sig n.λt. ∃i,outc.
  loopM sig n M i (initc sig n M t) = Some ? outc.
  
(* notation "M \vDash R" non associative with precedence 45 for @{ 'models $M $R}. *)
interpretation "multi realizability" 'models M R = (Realize ?? M R).

(* notation "M \VDash R" non associative with precedence 45 for @{ 'wmodels $M $R}. *)
interpretation "weak multi realizability" 'wmodels M R = (WRealize ?? M R).

interpretation "multi termination" 'fintersects M t = (Terminate ?? M t).

lemma WRealize_to_Realize : ∀sig,n .∀M: mTM sig n.∀R.
  (∀t.M ↓ t) → M ⊫ R → M ⊨ R.
#sig #n #M #R #HT #HW #t cases (HT … t) #i * #outc #Hloop 
@(ex_intro … i) @(ex_intro … outc) % // @(HW … i) //
qed.

theorem Realize_to_WRealize : ∀sig,n.∀M:mTM sig n.∀R.
  M ⊨ R → M ⊫ R.
#sig #n #M #R #H1 #inc #i #outc #Hloop 
cases (H1 inc) #k * #outc1 * #Hloop1 #HR >(loop_eq … Hloop Hloop1) //
qed.

definition accRealize ≝ λsig,n.λM:mTM sig n.λacc:states sig n M.λRtrue,Rfalse.
∀t.∃i.∃outc.
  loopM sig n M i (initc sig n M t) = Some ? outc ∧
    (cstate ??? outc = acc → Rtrue t (ctapes ??? outc)) ∧ 
    (cstate ??? outc ≠ acc → Rfalse t (ctapes ??? outc)).
    
(* notation "M ⊨ [q: R1,R2]" non associative with precedence 45 for @{ 'cmodels $M $q $R1 $R2}. *)
interpretation "conditional multi realizability" 'cmodels M q R1 R2 = (accRealize ?? M q R1 R2).

(*************************** guarded realizablity *****************************)
definition GRealize ≝ λsig,n.λM:mTM sig n.
 λPre:Vector (tape sig) ? →Prop.λR:relation (Vector (tape sig) ?).
  ∀t.Pre t → ∃i.∃outc.
   loopM sig n M i (initc sig n M t) = Some ? outc ∧ R t (ctapes ??? outc).
  
definition accGRealize ≝ λsig,n.λM:mTM sig n.λacc:states sig n M.
λPre: Vector (tape sig) ? → Prop.λRtrue,Rfalse.
∀t.Pre t → ∃i.∃outc.
  loopM sig n M i (initc sig n M t) = Some ? outc ∧
    (cstate ??? outc = acc → Rtrue t (ctapes ??? outc)) ∧ 
    (cstate ??? outc ≠ acc → Rfalse t (ctapes ??? outc)).
    
lemma WRealize_to_GRealize : ∀sig,n.∀M: mTM sig n.∀Pre,R.
  (∀t.Pre t → M ↓ t) → M ⊫ R → GRealize sig n M Pre R.
#sig #n #M #Pre #R #HT #HW #t #HPre cases (HT … t HPre) #i * #outc #Hloop 
@(ex_intro … i) @(ex_intro … outc) % // @(HW … i) //
qed.

lemma Realize_to_GRealize : ∀sig,n.∀M: mTM sig n.∀P,R. 
  M ⊨ R → GRealize sig n M P R.
#alpha #n #M #Pre #R #HR #t #HPre
cases (HR t) -HR #k * #outc * #Hloop #HR 
@(ex_intro ?? k) @(ex_intro ?? outc) % 
  [ @Hloop | @HR ]
qed.

lemma acc_Realize_to_acc_GRealize: ∀sig,n.∀M:mTM sig n.∀q:states sig n M.∀P,R1,R2. 
  M ⊨ [q:R1,R2] → accGRealize sig n M q P R1 R2.
#alpha #n #M #q #Pre #R1 #R2 #HR #t #HPre
cases (HR t) -HR #k * #outc * * #Hloop #HRtrue #HRfalse 
@(ex_intro ?? k) @(ex_intro ?? outc) % 
  [ % [@Hloop] @HRtrue | @HRfalse]
qed.

(******************************** monotonicity ********************************)
lemma Realize_to_Realize : ∀sig,n.∀M:mTM sig n.∀R1,R2.
  R1 ⊆ R2 → M ⊨ R1 → M ⊨ R2.
#alpha #n #M #R1 #R2 #Himpl #HR1 #intape
cases (HR1 intape) -HR1 #k * #outc * #Hloop #HR1
@(ex_intro ?? k) @(ex_intro ?? outc) % /2/
qed.

lemma WRealize_to_WRealize: ∀sig,n.∀M:mTM sig n.∀R1,R2.
  R1 ⊆ R2 → WRealize sig n M R1 → WRealize sig n M R2.
#alpha #n #M #R1 #R2 #Hsub #HR1 #intape #i #outc #Hloop
@Hsub @(HR1 … i) @Hloop
qed.

lemma GRealize_to_GRealize : ∀sig,n.∀M:mTM sig n.∀P,R1,R2.
  R1 ⊆ R2 → GRealize sig n M P R1 → GRealize sig n M P R2.
#alpha #n #M #P #R1 #R2 #Himpl #HR1 #intape #HP
cases (HR1 intape HP) -HR1 #k * #outc * #Hloop #HR1
@(ex_intro ?? k) @(ex_intro ?? outc) % /2/
qed.

lemma GRealize_to_GRealize_2 : ∀sig,n.∀M:mTM sig n.∀P1,P2,R1,R2.
  P2 ⊆ P1 → R1 ⊆ R2 → GRealize sig n M P1 R1 → GRealize sig n M P2 R2.
#alpha #n #M #P1 #P2 #R1 #R2 #Himpl1 #Himpl2 #H1 #intape #HP
cases (H1 intape (Himpl1 … HP)) -H1 #k * #outc * #Hloop #H1
@(ex_intro ?? k) @(ex_intro ?? outc) % /2/
qed.

lemma acc_Realize_to_acc_Realize: ∀sig,n.∀M:mTM sig n.∀q:states sig n M.
 ∀R1,R2,R3,R4. 
  R1 ⊆ R3 → R2 ⊆ R4 → M ⊨ [q:R1,R2] → M ⊨ [q:R3,R4].
#alpha #n #M #q #R1 #R2 #R3 #R4 #Hsub13 #Hsub24 #HRa #intape
cases (HRa intape) -HRa #k * #outc * * #Hloop #HRtrue #HRfalse 
@(ex_intro ?? k) @(ex_intro ?? outc) % 
  [ % [@Hloop] #Hq @Hsub13 @HRtrue // | #Hq @Hsub24 @HRfalse //]
qed.

(**************************** A canonical relation ****************************)

definition R_mTM ≝ λsig,n.λM:mTM sig n.λq.λt1,t2.
∃i,outc.
  loopM ? n M i (mk_mconfig ??? q t1) = Some ? outc ∧ 
  t2 = (ctapes ??? outc).
  
lemma R_mTM_to_R: ∀sig,n.∀M:mTM sig n.∀R. ∀t1,t2. 
  M ⊫ R → R_mTM ?? M (start sig n M) t1 t2 → R t1 t2.
#sig #n #M #R #t1 #t2 whd in ⊢ (%→?); #HMR * #i * #outc *
#Hloop #Ht2 >Ht2 @(HMR … Hloop)
qed.

(******************************** NOP Machine *********************************)

(* NO OPERATION
   t1 = t2 
  
definition nop_states ≝ initN 1.
definition start_nop : initN 1 ≝ mk_Sig ?? 0 (le_n … 1). *)

definition nop ≝ 
  λalpha:FinSet.λn.mk_mTM alpha n nop_states
  (λp.let 〈q,a〉 ≝ p in 〈q,mk_Vector ? (S n) (make_list ? (〈None ?,N〉) (S n)) ?〉)
  start_nop (λ_.true).
elim n normalize //
qed.
  
definition R_nop ≝ λalpha,n.λt1,t2:Vector (tape alpha) (S n).t2 = t1.

lemma sem_nop :
  ∀alpha,n.nop alpha n⊨ R_nop alpha n.
#alpha #n #intapes @(ex_intro ?? 1) 
@(ex_intro … (mk_mconfig ??? start_nop intapes)) % % 
qed.

lemma nop_single_state: ∀sig,n.∀q1,q2:states ? n (nop sig n). q1 = q2.
normalize #sig #n0 * #n #ltn1 * #m #ltm1 
generalize in match ltn1; generalize in match ltm1;
<(le_n_O_to_eq … (le_S_S_to_le … ltn1)) <(le_n_O_to_eq … (le_S_S_to_le … ltm1)) 
// qed.

(************************** Sequential Composition ****************************)
definition null_action ≝ λsig.λn.
mk_Vector ? (S n) (make_list (option sig × move) (〈None ?,N〉) (S n)) ?.
elim (S n) // normalize //
qed.

lemma tape_move_null_action: ∀sig,n,tapes.
  tape_move_multi sig (S n) tapes (null_action sig n) = tapes.
#sig #n #tapes cases tapes -tapes #tapes whd in match (null_action ??);
#Heq @Vector_eq <Heq -Heq elim tapes //
#a #tl #Hind whd in ⊢ (??%?); @eq_f2 // @Hind
qed.

definition seq_trans ≝ λsig,n. λM1,M2 : mTM sig n. 
λp. let 〈s,a〉 ≝ p in
  match s with 
  [ inl s1 ⇒ 
      if halt sig n M1 s1 then 〈inr … (start sig n M2), null_action sig n〉
      else let 〈news1,m〉 ≝ trans sig n M1 〈s1,a〉 in 〈inl … news1,m〉
  | inr s2 ⇒ let 〈news2,m〉 ≝ trans sig n M2 〈s2,a〉 in 〈inr … news2,m〉
  ].
 
definition seq ≝ λsig,n. λM1,M2 : mTM sig n. 
  mk_mTM sig n
    (FinSum (states sig n M1) (states sig n M2))
    (seq_trans sig n M1 M2) 
    (inl … (start sig n M1))
    (λs.match s with 
      [ inl _ ⇒ false | inr s2 ⇒ halt sig n M2 s2]). 

(* notation "a · b" right associative with precedence 65 for @{ 'middot $a $b}. *)
interpretation "sequential composition" 'middot a b = (seq ?? a b).

definition lift_confL ≝ 
  λsig,n,S1,S2,c.match c with 
  [ mk_mconfig s t ⇒ mk_mconfig sig (FinSum S1 S2) n (inl … s) t ].
  
definition lift_confR ≝ 
  λsig,n,S1,S2,c.match c with
  [ mk_mconfig s t ⇒ mk_mconfig sig (FinSum S1 S2) n (inr … s) t ].

(* 
definition halt_liftL ≝ 
  λS1,S2,halt.λs:FinSum S1 S2.
  match s with
  [ inl s1 ⇒ halt s1
  | inr _ ⇒ true ]. (* should be vacuous in all cases we use halt_liftL *)

definition halt_liftR ≝ 
  λS1,S2,halt.λs:FinSum S1 S2.
  match s with
  [ inl _ ⇒ false 
  | inr s2 ⇒ halt s2 ]. *)
      
lemma p_halt_liftL : ∀sig,n,S1,S2,halt,c.
  halt (cstate sig S1 n c) =
     halt_liftL S1 S2 halt (cstate … (lift_confL … c)).
#sig #n #S1 #S2 #halt #c cases c #s #t %
qed.

lemma trans_seq_liftL : ∀sig,n,M1,M2,s,a,news,move.
  halt ?? M1 s = false → 
  trans sig n M1 〈s,a〉 = 〈news,move〉 → 
  trans sig n (seq sig n M1 M2) 〈inl … s,a〉 = 〈inl … news,move〉.
#sig #n (*#M1*) * #Q1 #T1 #init1 #halt1 #M2 #s #a #news #move
#Hhalt #Htrans whd in ⊢ (??%?); >Hhalt >Htrans %
qed.

lemma trans_seq_liftR : ∀sig,n,M1,M2,s,a,news,move.
  halt ?? M2 s = false → 
  trans sig n M2 〈s,a〉 = 〈news,move〉 → 
  trans sig n (seq sig n M1 M2) 〈inr … s,a〉 = 〈inr … news,move〉.
#sig #n #M1 * #Q2 #T2 #init2 #halt2 #s #a #news #move
#Hhalt #Htrans whd in ⊢ (??%?); >Hhalt >Htrans %
qed.

lemma step_seq_liftR : ∀sig,n,M1,M2,c0.
 halt ?? M2 (cstate ??? c0) = false → 
 step sig n (seq sig n M1 M2) (lift_confR sig n (states ?? M1) (states ?? M2) c0) =
 lift_confR sig n (states ?? M1) (states ?? M2) (step sig n M2 c0).
#sig #n #M1 (* * #Q1 #T1 #init1 #halt1 *) #M2 * #s #t
lapply (refl ? (trans ??? 〈s,current_chars sig n t〉))
cases (trans ??? 〈s,current_chars sig n t〉) in ⊢ (???% → %);
#s0 #m0 #Heq #Hhalt whd in ⊢ (???(?????%)); >Heq  whd in ⊢ (???%);
whd in ⊢ (??(????%)?); whd in ⊢ (??%?); >(trans_seq_liftR … Heq) //
qed.

lemma step_seq_liftL : ∀sig,n,M1,M2,c0.
 halt ?? M1 (cstate ??? c0) = false → 
 step sig n (seq sig n M1 M2) (lift_confL sig n (states ?? M1) (states ?? M2) c0) =
 lift_confL sig n ?? (step sig n M1 c0).
#sig #n #M1 (* * #Q1 #T1 #init1 #halt1 *) #M2 * #s #t
  lapply (refl ? (trans ??? 〈s,current_chars sig n t〉))
  cases (trans ??? 〈s,current_chars sig n t〉) in ⊢ (???% → %);
  #s0 #m0 #Heq #Hhalt
  whd in ⊢ (???(?????%)); >Heq whd in ⊢ (???%);
  whd in ⊢ (??(????%)?); whd in ⊢ (??%?); >(trans_seq_liftL … Heq) //
qed.

lemma trans_liftL_true : ∀sig,n,M1,M2,s,a.
  halt ?? M1 s = true → 
  trans sig n (seq sig n M1 M2) 〈inl … s,a〉 = 〈inr … (start ?? M2),null_action sig n〉.
#sig #n #M1 #M2 #s #a #Hhalt whd in ⊢ (??%?); >Hhalt %
qed.

lemma eq_ctape_lift_conf_L : ∀sig,n,S1,S2,outc.
  ctapes sig (FinSum S1 S2) n (lift_confL … outc) = ctapes … outc.
#sig #n #S1 #S2 #outc cases outc #s #t %
qed.
  
lemma eq_ctape_lift_conf_R : ∀sig,n,S1,S2,outc.
  ctapes sig (FinSum S1 S2) n (lift_confR … outc) = ctapes … outc.
#sig #n #S1 #S2 #outc cases outc #s #t %
qed.

theorem sem_seq: ∀sig,n.∀M1,M2:mTM sig n.∀R1,R2.
  M1 ⊨ R1 → M2 ⊨ R2 → M1 · M2 ⊨ R1 ∘ R2.
#sig #n #M1 #M2 #R1 #R2 #HR1 #HR2 #t 
cases (HR1 t) #k1 * #outc1 * #Hloop1 #HM1
cases (HR2 (ctapes sig (states ?? M1) n outc1)) #k2 * #outc2 * #Hloop2 #HM2
@(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … outc2))
%
[@(loop_merge ??????????? 
   (loop_lift ??? (lift_confL sig n (states sig n M1) (states sig n M2))
   (step sig n M1) (step sig n (seq sig n M1 M2)) 
   (λc.halt sig n M1 (cstate … c)) 
   (λc.halt_liftL ?? (halt sig n M1) (cstate … c)) … Hloop1))
  [ * *
   [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
   | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
  || #c0 #Hhalt <step_seq_liftL //
  | #x <p_halt_liftL %
  |6:cases outc1 #s1 #t1 %
  |7:@(loop_lift … (initc ??? (ctapes … outc1)) … Hloop2) 
    [ * #s2 #t2 %
    | #c0 #Hhalt <step_seq_liftR // ]
  |whd in ⊢ (??(????%)?);whd in ⊢ (??%?);
   generalize in match Hloop1; cases outc1 #sc1 #tc1 #Hloop10 
   >(trans_liftL_true sig n M1 M2 ??) 
    [ whd in ⊢ (??%?); whd in ⊢ (???%);
      @mconfig_eq whd in ⊢ (???%); // 
    | @(loop_Some ?????? Hloop10) ]
 ]
| @(ex_intro … (ctapes ? (FinSum (states ?? M1) (states ?? M2)) ? (lift_confL … outc1)))
  % // >eq_ctape_lift_conf_L >eq_ctape_lift_conf_R //
]
qed.

theorem sem_seq_app: ∀sig,n.∀M1,M2:mTM sig n.∀R1,R2,R3.
  M1 ⊨ R1 → M2 ⊨ R2 → R1 ∘ R2 ⊆ R3 → M1 · M2 ⊨ R3.
#sig #n #M1 #M2 #R1 #R2 #R3 #HR1 #HR2 #Hsub
#t cases (sem_seq … HR1 HR2 t)
#k * #outc * #Hloop #Houtc @(ex_intro … k) @(ex_intro … outc)
% [@Hloop |@Hsub @Houtc]
qed.

(* composition with guards *)
theorem sem_seq_guarded: ∀sig,n.∀M1,M2:mTM sig n.∀Pre1,Pre2,R1,R2.
  GRealize sig n M1 Pre1 R1 → GRealize sig n M2 Pre2 R2 → 
  (∀t1,t2.Pre1 t1 → R1 t1 t2 → Pre2 t2) → 
  GRealize sig n (M1 · M2) Pre1 (R1 ∘ R2).
#sig #n #M1 #M2 #Pre1 #Pre2 #R1 #R2 #HGR1 #HGR2 #Hinv #t1 #HPre1
cases (HGR1 t1 HPre1) #k1 * #outc1 * #Hloop1 #HM1
cases (HGR2 (ctapes sig (states ?? M1) n outc1) ?) 
  [2: @(Hinv … HPre1 HM1)]  
#k2 * #outc2 * #Hloop2 #HM2
@(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … outc2))
%
[@(loop_merge ??????????? 
   (loop_lift ??? (lift_confL sig n (states sig n M1) (states sig n M2))
   (step sig n M1) (step sig n (seq sig n M1 M2)) 
   (λc.halt sig n M1 (cstate … c)) 
   (λc.halt_liftL ?? (halt sig n M1) (cstate … c)) … Hloop1))
  [ * *
   [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
   | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
  || #c0 #Hhalt <step_seq_liftL //
  | #x <p_halt_liftL %
  |6:cases outc1 #s1 #t1 %
  |7:@(loop_lift … (initc ??? (ctapes … outc1)) … Hloop2) 
    [ * #s2 #t2 %
    | #c0 #Hhalt <step_seq_liftR // ]
  |whd in ⊢ (??(????%)?);whd in ⊢ (??%?);
   generalize in match Hloop1; cases outc1 #sc1 #tc1 #Hloop10 
   >(trans_liftL_true sig n M1 M2 ??) 
    [ whd in ⊢ (??%?); whd in ⊢ (???%);
      @mconfig_eq whd in ⊢ (???%); //
    | @(loop_Some ?????? Hloop10) ]
 ]
| @(ex_intro … (ctapes ? (FinSum (states ?? M1) (states ?? M2)) n (lift_confL … outc1)))
  % // >eq_ctape_lift_conf_L >eq_ctape_lift_conf_R //
]
qed.

theorem sem_seq_app_guarded: ∀sig,n.∀M1,M2:mTM sig n.∀Pre1,Pre2,R1,R2,R3.
  GRealize sig n M1 Pre1 R1 → GRealize sig n M2 Pre2 R2 → 
  (∀t1,t2.Pre1 t1 → R1 t1 t2 → Pre2 t2) → R1 ∘ R2 ⊆ R3 →
  GRealize sig n (M1 · M2) Pre1 R3.
#sig #n #M1 #M2 #Pre1 #Pre2 #R1 #R2 #R3 #HR1 #HR2 #Hinv #Hsub
#t #HPre1 cases (sem_seq_guarded … HR1 HR2 Hinv t HPre1)
#k * #outc * #Hloop #Houtc @(ex_intro … k) @(ex_intro … outc)
% [@Hloop |@Hsub @Houtc]
qed.

theorem acc_sem_seq : ∀sig,n.∀M1,M2:mTM sig n.∀R1,Rtrue,Rfalse,acc.
  M1 ⊨ R1 → M2 ⊨ [ acc: Rtrue, Rfalse ] → 
  M1 · M2 ⊨ [ inr … acc: R1 ∘ Rtrue, R1 ∘ Rfalse ].
#sig #n #M1 #M2 #R1 #Rtrue #Rfalse #acc #HR1 #HR2 #t 
cases (HR1 t) #k1 * #outc1 * #Hloop1 #HM1
cases (HR2 (ctapes sig (states ?? M1) n outc1)) #k2 * #outc2 * * #Hloop2 
#HMtrue #HMfalse
@(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … outc2))
% [ %
[@(loop_merge ??????????? 
   (loop_lift ??? (lift_confL sig n (states sig n M1) (states sig n M2))
   (step sig n M1) (step sig n (seq sig n M1 M2)) 
   (λc.halt sig n M1 (cstate … c)) 
   (λc.halt_liftL ?? (halt sig n M1) (cstate … c)) … Hloop1))
  [ * *
   [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
   | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
  || #c0 #Hhalt <step_seq_liftL //
  | #x <p_halt_liftL %
  |6:cases outc1 #s1 #t1 %
  |7:@(loop_lift … (initc ??? (ctapes … outc1)) … Hloop2) 
    [ * #s2 #t2 %
    | #c0 #Hhalt <step_seq_liftR // ]
  |whd in ⊢ (??(????%)?);whd in ⊢ (??%?);
   generalize in match Hloop1; cases outc1 #sc1 #tc1 #Hloop10 
   >(trans_liftL_true sig n M1 M2 ??) 
    [ whd in ⊢ (??%?); whd in ⊢ (???%);
      @mconfig_eq whd in ⊢ (???%); // 
    | @(loop_Some ?????? Hloop10) ]
 ]
| >(mconfig_expand … outc2) in ⊢ (%→?); whd in ⊢ (??%?→?); 
  #Hqtrue destruct (Hqtrue)
  @(ex_intro … (ctapes ? (FinSum (states ?? M1) (states ?? M2)) ? (lift_confL … outc1)))
  % // >eq_ctape_lift_conf_L >eq_ctape_lift_conf_R /2/ ]
| >(mconfig_expand … outc2) in ⊢ (%→?); whd in ⊢ (?(??%?)→?); #Hqfalse
  @(ex_intro … (ctapes ? (FinSum (states ?? M1) (states ?? M2)) ? (lift_confL … outc1)))
  % // >eq_ctape_lift_conf_L >eq_ctape_lift_conf_R @HMfalse
  @(not_to_not … Hqfalse) //
]
qed.

lemma acc_sem_seq_app : ∀sig,n.∀M1,M2:mTM sig n.∀R1,Rtrue,Rfalse,R2,R3,acc.
  M1 ⊨ R1 → M2 ⊨ [acc: Rtrue, Rfalse] → 
    (∀t1,t2,t3. R1 t1 t3 → Rtrue t3 t2 → R2 t1 t2) → 
    (∀t1,t2,t3. R1 t1 t3 → Rfalse t3 t2 → R3 t1 t2) → 
    M1 · M2 ⊨ [inr … acc : R2, R3].    
#sig #n #M1 #M2 #R1 #Rtrue #Rfalse #R2 #R3 #acc
#HR1 #HRacc #Hsub1 #Hsub2 
#t cases (acc_sem_seq … HR1 HRacc t)
#k * #outc * * #Hloop #Houtc1 #Houtc2 @(ex_intro … k) @(ex_intro … outc)
% [% [@Hloop
     |#H cases (Houtc1 H) #t3 * #Hleft #Hright @Hsub1 // ]
  |#H cases (Houtc2 H) #t3 * #Hleft #Hright @Hsub2 // ]
qed.
