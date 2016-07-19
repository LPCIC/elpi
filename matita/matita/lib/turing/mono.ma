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

include "basics/finset.ma".
include "basics/vectors.ma".
include "basics/finset.ma".
(* include "basics/relations.ma". *)

(******************************** tape ****************************************)

(* A tape is essentially a triple 〈left,current,right〉 where however the current 
symbol could be missing. This may happen for three different reasons: both tapes 
are empty; we are on the left extremity of a non-empty tape (left overflow), or 
we are on the right extremity of a non-empty tape (right overflow). *)

inductive tape (sig:FinSet) : Type[0] ≝ 
| niltape : tape sig
| leftof  : sig → list sig → tape sig
| rightof : sig → list sig → tape sig
| midtape : list sig → sig → list sig → tape sig.

definition left ≝ 
 λsig.λt:tape sig.match t with
 [ niltape ⇒ [] | leftof _ _ ⇒ [] | rightof s l ⇒ s::l | midtape l _ _ ⇒ l ].

definition right ≝ 
 λsig.λt:tape sig.match t with
 [ niltape ⇒ [] | leftof s r ⇒ s::r | rightof _ _ ⇒ []| midtape _ _ r ⇒ r ].
 
definition current ≝ 
 λsig.λt:tape sig.match t with
 [ midtape _ c _ ⇒ Some ? c | _ ⇒ None ? ].
 
definition mk_tape : 
  ∀sig:FinSet.list sig → option sig → list sig → tape sig ≝ 
  λsig,lt,c,rt.match c with
  [ Some c' ⇒ midtape sig lt c' rt
  | None ⇒ match lt with 
    [ nil ⇒ match rt with
      [ nil ⇒ niltape ?
      | cons r0 rs0 ⇒ leftof ? r0 rs0 ]
    | cons l0 ls0 ⇒ rightof ? l0 ls0 ] ].

lemma right_mk_tape : 
  ∀sig,ls,c,rs.(c = None ? → ls = [ ] ∨ rs = [ ]) → right ? (mk_tape sig ls c rs) = rs.
#sig #ls #c #rs cases c // cases ls 
[ cases rs // 
| #l0 #ls0 #H normalize cases (H (refl ??)) #H1 [ destruct (H1) | >H1 % ] ]
qed-.

lemma left_mk_tape : ∀sig,ls,c,rs.left ? (mk_tape sig ls c rs) = ls.
#sig #ls #c #rs cases c // cases ls // cases rs //
qed.

lemma current_mk_tape : ∀sig,ls,c,rs.current ? (mk_tape sig ls c rs) = c.
#sig #ls #c #rs cases c // cases ls // cases rs //
qed.

lemma current_to_midtape: ∀sig,t,c. current sig t = Some ? c →
  ∃ls,rs. t = midtape ? ls c rs.
#sig *
  [#c whd in ⊢ ((??%?)→?); #Hfalse destruct
  |#a #l #c whd in ⊢ ((??%?)→?); #Hfalse destruct
  |#a #l #c whd in ⊢ ((??%?)→?); #Hfalse destruct
  |#ls #a #rs #c whd in ⊢ ((??%?)→?); #H destruct 
   @(ex_intro … ls) @(ex_intro … rs) //
  ]
qed.

(*********************************** moves ************************************)

inductive move : Type[0] ≝
  | L : move | R : move | N : move.
  
(*************************** turning moves into a DeqSet **********************)

definition move_eq ≝ λm1,m2:move.
  match m1 with
  [R ⇒ match m2 with [R ⇒ true | _ ⇒ false]
  |L ⇒ match m2 with [L ⇒ true | _ ⇒ false]
  |N ⇒ match m2 with [N ⇒ true | _ ⇒ false]].

lemma move_eq_true:∀m1,m2.
  move_eq m1 m2 = true ↔ m1 = m2.
*
  [* normalize [% #_ % |2,3: % #H destruct ]
  |* normalize [1,3: % #H destruct |% #_ % ]
  |* normalize [1,2: % #H destruct |% #_ % ]
qed.

definition DeqMove ≝ mk_DeqSet move move_eq move_eq_true.

unification hint 0 ≔ ;
    X ≟ DeqMove
(* ---------------------------------------- *) ⊢ 
    move ≡ carr X.

unification hint  0 ≔ m1,m2; 
    X ≟ DeqMove
(* ---------------------------------------- *) ⊢ 
    move_eq m1 m2 ≡ eqb X m1 m2.


(************************ turning DeqMove into a FinSet ***********************)

definition move_enum ≝ [L;R;N].

lemma move_enum_unique: uniqueb ? [L;R;N] = true.
// qed.

lemma move_enum_complete: ∀x:move. memb ? x [L;R;N] = true.
* // qed.

definition FinMove ≝ 
  mk_FinSet DeqMove [L;R;N] move_enum_unique move_enum_complete.

unification hint  0 ≔ ; 
    X ≟ FinMove
(* ---------------------------------------- *) ⊢ 
    move ≡ FinSetcarr X.
(********************************** machine ***********************************)

record TM (sig:FinSet): Type[1] ≝ 
{ states : FinSet;
  trans : states × (option sig) → states × (option sig) × move;
  start: states;
  halt : states → bool
}.

definition tape_move_left ≝ λsig:FinSet.λt:tape sig.
  match t with 
  [ niltape ⇒ niltape sig
  | leftof _ _ ⇒ t
  | rightof a ls ⇒ midtape sig ls a [ ]
  | midtape ls a rs ⇒ 
    match ls with 
    [ nil ⇒ leftof sig a rs
    | cons a0 ls0 ⇒ midtape sig ls0 a0 (a::rs)
    ]
  ]. 
  
definition tape_move_right ≝ λsig:FinSet.λt:tape sig.
  match t with 
  [ niltape ⇒ niltape sig
  | rightof _ _ ⇒ t
  | leftof a rs ⇒ midtape sig [ ] a rs
  | midtape ls a rs ⇒ 
    match rs with 
    [ nil ⇒ rightof sig a ls
    | cons a0 rs0 ⇒ midtape sig (a::ls) a0 rs0
    ]
  ]. 
  
definition tape_write ≝ λsig.λt: tape sig.λs:option sig.
  match s with 
  [ None ⇒ t
  | Some s0 ⇒ midtape ? (left ? t) s0 (right ? t)
  ].

definition tape_move ≝ λsig.λt: tape sig.λm:move.
  match m with
    [ R ⇒ tape_move_right ? t
    | L ⇒ tape_move_left ? t
    | N ⇒ t
    ].

definition tape_move_mono ≝ 
  λsig,t,mv.
  tape_move sig (tape_write sig t (\fst mv)) (\snd mv).

record config (sig,states:FinSet): Type[0] ≝ 
{ cstate : states;
  ctape: tape sig
}.

lemma config_expand: ∀sig,Q,c. 
  c = mk_config sig Q (cstate ?? c) (ctape ?? c).
#sig #Q * // 
qed.
  
lemma config_eq : ∀sig,M,c1,c2.
  cstate sig M c1 = cstate sig M c2 → 
    ctape sig M c1 = ctape sig M c2 →  c1 = c2.
#sig #M1 * #s1 #t1 * #s2 #t2 //
qed.

definition step ≝ λsig.λM:TM sig.λc:config sig (states sig M).
  let current_char ≝ current ? (ctape ?? c) in
  let 〈news,a,mv〉 ≝ trans sig M 〈cstate ?? c,current_char〉 in
  mk_config ?? news (tape_move sig (tape_write ? (ctape ?? c) a) mv).

(*
lemma step_eq : ∀sig,M,c. 
  let current_char ≝ current ? (ctape ?? c) in
  let 〈news,a,mv〉 ≝ trans sig M 〈cstate ?? c,current_char〉 in
  step sig M c = 
    mk_config ?? news (tape_move sig (tape_write ? (ctape ?? c) a) mv).
#sig #M #c  
 whd in match (tape_move_mono sig ??);
*)
  
(******************************** loop ****************************************)
let rec loop (A:Type[0]) n (f:A→A) p a on n ≝
  match n with 
  [ O ⇒ None ?
  | S m ⇒ if p a then (Some ? a) else loop A m f p (f a)
  ].
  
lemma loop_S_true : 
  ∀A,n,f,p,a. p a = true → 
    loop A (S n) f p a = Some ? a.
#A #n #f #p #a #pa normalize >pa //
qed.

lemma loop_S_false : 
  ∀A,n,f,p,a.  p a = false → 
    loop A (S n) f p a = loop A n f p (f a).
normalize #A #n #f #p #a #Hpa >Hpa %
qed.  
  
lemma loop_incr : ∀A,f,p,k1,k2,a1,a2. 
  loop A k1 f p a1 = Some ? a2 → 
    loop A (k2+k1) f p a1 = Some ? a2.
#A #f #p #k1 #k2 #a1 #a2 generalize in match a1; elim k1
[normalize #a0 #Hfalse destruct
|#k1' #IH #a0 <plus_n_Sm whd in ⊢ (??%? → ??%?);
 cases (true_or_false (p a0)) #Hpa0 >Hpa0 whd in ⊢ (??%? → ??%?); // @IH
]
qed.

lemma loop_merge : ∀A,f,p,q.(∀b. p b = false → q b = false) →
 ∀k1,k2,a1,a2,a3,a4.
   loop A k1 f p a1 = Some ? a2 → 
     f a2 = a3 → q a2 = false → 
       loop A k2 f q a3 = Some ? a4 →
         loop A (k1+k2) f q a1 = Some ? a4.
#Sig #f #p #q #Hpq #k1 elim k1 
  [normalize #k2 #a1 #a2 #a3 #a4 #H destruct
  |#k1' #Hind #k2 #a1 #a2 #a3 #a4 normalize in ⊢ (%→?);
   cases (true_or_false (p a1)) #pa1 >pa1 normalize in ⊢ (%→?);
   [#eqa1a2 destruct #eqa2a3 #Hqa2 #H
    whd in ⊢ (??(??%???)?); >plus_n_Sm @loop_incr
    whd in ⊢ (??%?); >Hqa2 >eqa2a3 @H
   |normalize >(Hpq … pa1) normalize #H1 #H2 #H3 @(Hind … H2) //
   ]
 ]
qed.

lemma loop_split : ∀A,f,p,q.(∀b. q b = true → p b = true) →
 ∀k,a1,a2.
   loop A k f q a1 = Some ? a2 → 
   ∃k1,a3.
    loop A k1 f p a1 = Some ? a3 ∧ 
      loop A (S(k-k1)) f q a3 = Some ? a2.
#A #f #p #q #Hpq #k elim k
  [#a1 #a2 normalize #Heq destruct
  |#i #Hind #a1 #a2 normalize 
   cases (true_or_false (q a1)) #Hqa1 >Hqa1 normalize
    [ #Ha1a2 destruct
     @(ex_intro … 1) @(ex_intro … a2) % 
       [normalize >(Hpq …Hqa1) // |>Hqa1 //]
    |#Hloop cases (true_or_false (p a1)) #Hpa1 
       [@(ex_intro … 1) @(ex_intro … a1) % 
         [normalize >Hpa1 // |>Hqa1 <Hloop normalize //]
       |cases (Hind …Hloop) #k2 * #a3 * #Hloop1 #Hloop2
        @(ex_intro … (S k2)) @(ex_intro … a3) %
         [normalize >Hpa1 normalize // | @Hloop2 ]
       ]
    ]
  ]
qed.

lemma loop_eq : ∀sig,f,q,i,j,a,x,y. 
  loop sig i f q a = Some ? x → loop sig j f q a = Some ? y → x = y.
#sig #f #q #i #j @(nat_elim2 … i j)
[ #n #a #x #y normalize #Hfalse destruct (Hfalse)
| #n #a #x #y #H1 normalize #Hfalse destruct (Hfalse)
| #n1 #n2 #IH #a #x #y normalize cases (q a) normalize
  [ #H1 #H2 destruct %
  | /2/ ]
]
qed.

lemma loop_p_true : 
  ∀A,k,f,p,a.p a = true → loop A (S k) f p a = Some ? a.
#A #k #f #p #a #Ha normalize >Ha %
qed.

lemma loop_Some : 
  ∀A,k,f,p,a,b.loop A k f p a = Some ? b → p b = true.
#A #k #f #p elim k 
  [#a #b normalize #Hfalse destruct
  |#k0 #IH #a #b whd in ⊢ (??%? → ?); cases (true_or_false (p a)) #Hpa
    [ >Hpa normalize #H1 destruct // | >Hpa normalize @IH ]
  ]
qed. 

lemma loop_lift : ∀A,B,k,lift,f,g,h,hlift,c1,c2.
  (∀x.hlift (lift x) = h x) → 
  (∀x.h x = false → lift (f x) = g (lift x)) → 
  loop A k f h c1 = Some ? c2 → 
  loop B k g hlift (lift c1) = Some ? (lift … c2).
#A #B #k #lift #f #g #h #hlift #c1 #c2 #Hfg #Hhlift
generalize in match c1; elim k
[#c0 normalize in ⊢ (??%? → ?); #Hfalse destruct (Hfalse)
|#k0 #IH #c0 whd in ⊢ (??%? → ??%?);
 cases (true_or_false (h c0)) #Hc0 >Hfg >Hc0 normalize
 [ #Heq destruct (Heq) % | <Hhlift // @IH ]
qed.

(************************** Realizability *************************************)
definition loopM ≝ λsig,M,i,cin.
  loop ? i (step sig M) (λc.halt sig M (cstate ?? c)) cin.

lemma loopM_unfold : ∀sig,M,i,cin.
  loopM sig M i cin = loop ? i (step sig M) (λc.halt sig M (cstate ?? c)) cin.
// qed.

definition initc ≝ λsig.λM:TM sig.λt.
  mk_config sig (states sig M) (start sig M) t.

definition Realize ≝ λsig.λM:TM sig.λR:relation (tape sig).
∀t.∃i.∃outc.
  loopM sig M i (initc sig M t) = Some ? outc ∧ R t (ctape ?? outc).

definition WRealize ≝ λsig.λM:TM sig.λR:relation (tape sig).
∀t,i,outc.
  loopM sig M i (initc sig M t) = Some ? outc → R t (ctape ?? outc).

definition Terminate ≝ λsig.λM:TM sig.λt. ∃i,outc.
  loopM sig M i (initc sig M t) = Some ? outc.
  
notation "M \vDash R" non associative with precedence 45 for @{ 'models $M $R}.
interpretation "realizability" 'models M R = (Realize ? M R).

notation "M \VDash R" non associative with precedence 45 for @{ 'wmodels $M $R}.
interpretation "weak realizability" 'wmodels M R = (WRealize ? M R).

interpretation "termination" 'fintersects M t = (Terminate ? M t).

lemma WRealize_to_Realize : ∀sig.∀M: TM sig.∀R.
  (∀t.M ↓ t) → M ⊫ R → M ⊨ R.
#sig #M #R #HT #HW #t cases (HT … t) #i * #outc #Hloop 
@(ex_intro … i) @(ex_intro … outc) % // @(HW … i) //
qed.

theorem Realize_to_WRealize : ∀sig.∀M:TM sig.∀R.
  M ⊨ R → M ⊫ R.
#sig #M #R #H1 #inc #i #outc #Hloop 
cases (H1 inc) #k * #outc1 * #Hloop1 #HR >(loop_eq … Hloop Hloop1) //
qed.

definition accRealize ≝ λsig.λM:TM sig.λacc:states sig M.λRtrue,Rfalse.
∀t.∃i.∃outc.
  loopM sig M i (initc sig M t) = Some ? outc ∧
    (cstate ?? outc = acc → Rtrue t (ctape ?? outc)) ∧ 
    (cstate ?? outc ≠ acc → Rfalse t (ctape ?? outc)).
    
notation "M ⊨ [q: R1,R2]" non associative with precedence 45 for @{ 'cmodels $M $q $R1 $R2}.
interpretation "conditional realizability" 'cmodels M q R1 R2 = (accRealize ? M q R1 R2).

(*************************** guarded realizablity *****************************)
definition GRealize ≝ λsig.λM:TM sig.λPre:tape sig →Prop.λR:relation (tape sig).
∀t.Pre t → ∃i.∃outc.
  loopM sig M i (initc sig M t) = Some ? outc ∧ R t (ctape ?? outc).
  
definition accGRealize ≝ λsig.λM:TM sig.λacc:states sig M.
λPre: tape sig → Prop.λRtrue,Rfalse.
∀t.Pre t → ∃i.∃outc.
  loopM sig M i (initc sig M t) = Some ? outc ∧
    (cstate ?? outc = acc → Rtrue t (ctape ?? outc)) ∧ 
    (cstate ?? outc ≠ acc → Rfalse t (ctape ?? outc)).
    
lemma WRealize_to_GRealize : ∀sig.∀M: TM sig.∀Pre,R.
  (∀t.Pre t → M ↓ t) → M ⊫ R → GRealize sig M Pre R.
#sig #M #Pre #R #HT #HW #t #HPre cases (HT … t HPre) #i * #outc #Hloop 
@(ex_intro … i) @(ex_intro … outc) % // @(HW … i) //
qed.

lemma Realize_to_GRealize : ∀sig,M.∀P,R. 
  M ⊨ R → GRealize sig M P R.
#alpha #M #Pre #R #HR #t #HPre
cases (HR t) -HR #k * #outc * #Hloop #HR 
@(ex_intro ?? k) @(ex_intro ?? outc) % 
  [ @Hloop | @HR ]
qed.

lemma acc_Realize_to_acc_GRealize: ∀sig,M.∀q:states sig M.∀P,R1,R2. 
  M ⊨ [q:R1,R2] → accGRealize sig M q P R1 R2.
#alpha #M #q #Pre #R1 #R2 #HR #t #HPre
cases (HR t) -HR #k * #outc * * #Hloop #HRtrue #HRfalse 
@(ex_intro ?? k) @(ex_intro ?? outc) % 
  [ % [@Hloop] @HRtrue | @HRfalse]
qed.

(******************************** monotonicity ********************************)
lemma Realize_to_Realize : ∀alpha,M,R1,R2.
  R1 ⊆ R2 → Realize alpha M R1 → Realize alpha M R2.
#alpha #M #R1 #R2 #Himpl #HR1 #intape
cases (HR1 intape) -HR1 #k * #outc * #Hloop #HR1
@(ex_intro ?? k) @(ex_intro ?? outc) % /2/
qed.

lemma WRealize_to_WRealize: ∀sig,M,R1,R2.
  R1 ⊆ R2 → WRealize sig M R1 → WRealize ? M R2.
#alpha #M #R1 #R2 #Hsub #HR1 #intape #i #outc #Hloop
@Hsub @(HR1 … i) @Hloop
qed.

lemma GRealize_to_GRealize : ∀alpha,M,P,R1,R2.
  R1 ⊆ R2 → GRealize alpha M P R1 → GRealize alpha M P R2.
#alpha #M #P #R1 #R2 #Himpl #HR1 #intape #HP
cases (HR1 intape HP) -HR1 #k * #outc * #Hloop #HR1
@(ex_intro ?? k) @(ex_intro ?? outc) % /2/
qed.

lemma GRealize_to_GRealize_2 : ∀alpha,M,P1,P2,R1,R2.
  P2 ⊆ P1 → R1 ⊆ R2 → GRealize alpha M P1 R1 → GRealize alpha M P2 R2.
#alpha #M #P1 #P2 #R1 #R2 #Himpl1 #Himpl2 #H1 #intape #HP
cases (H1 intape (Himpl1 … HP)) -H1 #k * #outc * #Hloop #H1
@(ex_intro ?? k) @(ex_intro ?? outc) % /2/
qed.

lemma acc_Realize_to_acc_Realize: ∀sig,M.∀q:states sig M.∀R1,R2,R3,R4. 
  R1 ⊆ R3 → R2 ⊆ R4 → M ⊨ [q:R1,R2] → M ⊨ [q:R3,R4].
#alpha #M #q #R1 #R2 #R3 #R4 #Hsub13 #Hsub24 #HRa #intape
cases (HRa intape) -HRa #k * #outc * * #Hloop #HRtrue #HRfalse 
@(ex_intro ?? k) @(ex_intro ?? outc) % 
  [ % [@Hloop] #Hq @Hsub13 @HRtrue // | #Hq @Hsub24 @HRfalse //]
qed.

(**************************** A canonical relation ****************************)

definition R_TM ≝ λsig.λM:TM sig.λq.λt1,t2.
∃i,outc.
  loopM ? M i (mk_config ?? q t1) = Some ? outc ∧ 
  t2 = (ctape ?? outc).
  
lemma R_TM_to_R: ∀sig,M,R. ∀t1,t2. 
  M ⊫ R → R_TM ? M (start sig M) t1 t2 → R t1 t2.
#sig #M #R #t1 #t2 whd in ⊢ (%→?); #HMR * #i * #outc *
#Hloop #Ht2 >Ht2 @(HMR … Hloop)
qed.

(******************************** NOP Machine *********************************)

(* NO OPERATION
   t1 = t2 *)
  
definition nop_states ≝ initN 1.
definition start_nop : initN 1 ≝ mk_Sig ?? 0 (le_n … 1).

definition nop ≝ 
  λalpha:FinSet.mk_TM alpha nop_states
  (λp.let 〈q,a〉 ≝ p in 〈q,None ?,N〉)
  start_nop (λ_.true).
  
definition R_nop ≝ λalpha.λt1,t2:tape alpha.t2 = t1.

lemma sem_nop :
  ∀alpha.nop alpha ⊨ R_nop alpha.
#alpha #intape @(ex_intro ?? 1) 
@(ex_intro … (mk_config ?? start_nop intape)) % % 
qed.

lemma nop_single_state: ∀sig.∀q1,q2:states ? (nop sig). q1 = q2.
normalize #sig * #n #ltn1 * #m #ltm1 
generalize in match ltn1; generalize in match ltm1;
<(le_n_O_to_eq … (le_S_S_to_le … ltn1)) <(le_n_O_to_eq … (le_S_S_to_le … ltm1)) 
// qed.

(************************** Sequential Composition ****************************)

definition seq_trans ≝ λsig. λM1,M2 : TM sig. 
λp. let 〈s,a〉 ≝ p in
  match s with 
  [ inl s1 ⇒ 
      if halt sig M1 s1 then 〈inr … (start sig M2), None ?,N〉
      else let 〈news1,newa,m〉 ≝ trans sig M1 〈s1,a〉 in 〈inl … news1,newa,m〉
  | inr s2 ⇒ let 〈news2,newa,m〉 ≝ trans sig M2 〈s2,a〉 in 〈inr … news2,newa,m〉
  ].
 
definition seq ≝ λsig. λM1,M2 : TM sig. 
  mk_TM sig 
    (FinSum (states sig M1) (states sig M2))
    (seq_trans sig M1 M2) 
    (inl … (start sig M1))
    (λs.match s with 
      [ inl _ ⇒ false | inr s2 ⇒ halt sig M2 s2]). 

notation "a · b" right associative with precedence 65 for @{ 'middot $a $b}.
interpretation "sequential composition" 'middot a b = (seq ? a b).

definition lift_confL ≝ 
  λsig,S1,S2,c.match c with 
  [ mk_config s t ⇒ mk_config sig (FinSum S1 S2) (inl … s) t ].
  
definition lift_confR ≝ 
  λsig,S1,S2,c.match c with
  [ mk_config s t ⇒ mk_config sig (FinSum S1 S2) (inr … s) t ].
  
definition halt_liftL ≝ 
  λS1,S2,halt.λs:FinSum S1 S2.
  match s with
  [ inl s1 ⇒ halt s1
  | inr _ ⇒ true ]. (* should be vacuous in all cases we use halt_liftL *)

definition halt_liftR ≝ 
  λS1,S2,halt.λs:FinSum S1 S2.
  match s with
  [ inl _ ⇒ false 
  | inr s2 ⇒ halt s2 ].
      
lemma p_halt_liftL : ∀sig,S1,S2,halt,c.
  halt (cstate sig S1 c) =
     halt_liftL S1 S2 halt (cstate … (lift_confL … c)).
#sig #S1 #S2 #halt #c cases c #s #t %
qed.

lemma trans_seq_liftL : ∀sig,M1,M2,s,a,news,newa,move.
  halt ? M1 s = false → 
  trans sig M1 〈s,a〉 = 〈news,newa,move〉 → 
  trans sig (seq sig M1 M2) 〈inl … s,a〉 = 〈inl … news,newa,move〉.
#sig (*#M1*) * #Q1 #T1 #init1 #halt1 #M2 #s #a #news #newa #move
#Hhalt #Htrans whd in ⊢ (??%?); >Hhalt >Htrans %
qed.

lemma trans_seq_liftR : ∀sig,M1,M2,s,a,news,newa,move.
  halt ? M2 s = false → 
  trans sig M2 〈s,a〉 = 〈news,newa,move〉 → 
  trans sig (seq sig M1 M2) 〈inr … s,a〉 = 〈inr … news,newa,move〉.
#sig #M1 * #Q2 #T2 #init2 #halt2 #s #a #news #newa #move
#Hhalt #Htrans whd in ⊢ (??%?); >Hhalt >Htrans %
qed.

lemma step_seq_liftR : ∀sig,M1,M2,c0.
 halt ? M2 (cstate ?? c0) = false → 
 step sig (seq sig M1 M2) (lift_confR sig (states ? M1) (states ? M2) c0) =
 lift_confR sig (states ? M1) (states ? M2) (step sig M2 c0).
#sig #M1 (* * #Q1 #T1 #init1 #halt1 *) #M2 * #s #t
  lapply (refl ? (trans ?? 〈s,current sig t〉))
  cases (trans ?? 〈s,current sig t〉) in ⊢ (???% → %);
  * #s0 #a0 #m0 cases t
  [ #Heq #Hhalt
  | 2,3: #s1 #l1 #Heq #Hhalt 
  |#ls #s1 #rs #Heq #Hhalt ]
  whd in ⊢ (???(????%)); >Heq whd in ⊢ (???%);
  whd in ⊢ (??(???%)?); whd in ⊢ (??%?); >(trans_seq_liftR … Heq) //
qed.

lemma step_seq_liftL : ∀sig,M1,M2,c0.
 halt ? M1 (cstate ?? c0) = false → 
 step sig (seq sig M1 M2) (lift_confL sig (states ? M1) (states ? M2) c0) =
 lift_confL sig ?? (step sig M1 c0).
#sig #M1 (* * #Q1 #T1 #init1 #halt1 *) #M2 * #s #t
  lapply (refl ? (trans ?? 〈s,current sig t〉))
  cases (trans ?? 〈s,current sig t〉) in ⊢ (???% → %);
  * #s0 #a0 #m0 cases t
  [ #Heq #Hhalt
  | 2,3: #s1 #l1 #Heq #Hhalt 
  |#ls #s1 #rs #Heq #Hhalt ]
  whd in ⊢ (???(????%)); >Heq whd in ⊢ (???%);
  whd in ⊢ (??(???%)?); whd in ⊢ (??%?); >(trans_seq_liftL … Heq) //
qed.

lemma trans_liftL_true : ∀sig,M1,M2,s,a.
  halt ? M1 s = true → 
  trans sig (seq sig M1 M2) 〈inl … s,a〉 = 〈inr … (start ? M2),None ?,N〉.
#sig #M1 #M2 #s #a #Hhalt whd in ⊢ (??%?); >Hhalt %
qed.

lemma eq_ctape_lift_conf_L : ∀sig,S1,S2,outc.
  ctape sig (FinSum S1 S2) (lift_confL … outc) = ctape … outc.
#sig #S1 #S2 #outc cases outc #s #t %
qed.
  
lemma eq_ctape_lift_conf_R : ∀sig,S1,S2,outc.
  ctape sig (FinSum S1 S2) (lift_confR … outc) = ctape … outc.
#sig #S1 #S2 #outc cases outc #s #t %
qed.

theorem sem_seq: ∀sig.∀M1,M2:TM sig.∀R1,R2.
  M1 ⊨ R1 → M2 ⊨ R2 → M1 · M2 ⊨ R1 ∘ R2.
#sig #M1 #M2 #R1 #R2 #HR1 #HR2 #t 
cases (HR1 t) #k1 * #outc1 * #Hloop1 #HM1
cases (HR2 (ctape sig (states ? M1) outc1)) #k2 * #outc2 * #Hloop2 #HM2
@(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … outc2))
%
[@(loop_merge ??????????? 
   (loop_lift ??? (lift_confL sig (states sig M1) (states sig M2))
   (step sig M1) (step sig (seq sig M1 M2)) 
   (λc.halt sig M1 (cstate … c)) 
   (λc.halt_liftL ?? (halt sig M1) (cstate … c)) … Hloop1))
  [ * *
   [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
   | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
  || #c0 #Hhalt <step_seq_liftL //
  | #x <p_halt_liftL %
  |6:cases outc1 #s1 #t1 %
  |7:@(loop_lift … (initc ?? (ctape … outc1)) … Hloop2) 
    [ * #s2 #t2 %
    | #c0 #Hhalt <step_seq_liftR // ]
  |whd in ⊢ (??(???%)?);whd in ⊢ (??%?);
   generalize in match Hloop1; cases outc1 #sc1 #tc1 #Hloop10 
   >(trans_liftL_true sig M1 M2 ??) 
    [ whd in ⊢ (??%?); whd in ⊢ (???%);
      @config_eq whd in ⊢ (???%); //
    | @(loop_Some ?????? Hloop10) ]
 ]
| @(ex_intro … (ctape ? (FinSum (states ? M1) (states ? M2)) (lift_confL … outc1)))
  % // >eq_ctape_lift_conf_L >eq_ctape_lift_conf_R //
]
qed.

theorem sem_seq_app: ∀sig.∀M1,M2:TM sig.∀R1,R2,R3.
  M1 ⊨ R1 → M2 ⊨ R2 → R1 ∘ R2 ⊆ R3 → M1 · M2 ⊨ R3.
#sig #M1 #M2 #R1 #R2 #R3 #HR1 #HR2 #Hsub
#t cases (sem_seq … HR1 HR2 t)
#k * #outc * #Hloop #Houtc @(ex_intro … k) @(ex_intro … outc)
% [@Hloop |@Hsub @Houtc]
qed.

(* composition with guards *)
theorem sem_seq_guarded: ∀sig.∀M1,M2:TM sig.∀Pre1,Pre2,R1,R2.
  GRealize sig M1 Pre1 R1 → GRealize sig M2 Pre2 R2 → 
  (∀t1,t2.Pre1 t1 → R1 t1 t2 → Pre2 t2) → 
  GRealize sig (M1 · M2) Pre1 (R1 ∘ R2).
#sig #M1 #M2 #Pre1 #Pre2 #R1 #R2 #HGR1 #HGR2 #Hinv #t1 #HPre1
cases (HGR1 t1 HPre1) #k1 * #outc1 * #Hloop1 #HM1
cases (HGR2 (ctape sig (states ? M1) outc1) ?) 
  [2: @(Hinv … HPre1 HM1)]  
#k2 * #outc2 * #Hloop2 #HM2
@(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … outc2))
%
[@(loop_merge ??????????? 
   (loop_lift ??? (lift_confL sig (states sig M1) (states sig M2))
   (step sig M1) (step sig (seq sig M1 M2)) 
   (λc.halt sig M1 (cstate … c)) 
   (λc.halt_liftL ?? (halt sig M1) (cstate … c)) … Hloop1))
  [ * *
   [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
   | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
  || #c0 #Hhalt <step_seq_liftL //
  | #x <p_halt_liftL %
  |6:cases outc1 #s1 #t1 %
  |7:@(loop_lift … (initc ?? (ctape … outc1)) … Hloop2) 
    [ * #s2 #t2 %
    | #c0 #Hhalt <step_seq_liftR // ]
  |whd in ⊢ (??(???%)?);whd in ⊢ (??%?);
   generalize in match Hloop1; cases outc1 #sc1 #tc1 #Hloop10 
   >(trans_liftL_true sig M1 M2 ??) 
    [ whd in ⊢ (??%?); whd in ⊢ (???%);
      @config_eq whd in ⊢ (???%); //
    | @(loop_Some ?????? Hloop10) ]
 ]
| @(ex_intro … (ctape ? (FinSum (states ? M1) (states ? M2)) (lift_confL … outc1)))
  % // >eq_ctape_lift_conf_L >eq_ctape_lift_conf_R //
]
qed.

theorem sem_seq_app_guarded: ∀sig.∀M1,M2:TM sig.∀Pre1,Pre2,R1,R2,R3.
  GRealize sig M1 Pre1 R1 → GRealize sig M2 Pre2 R2 → 
  (∀t1,t2.Pre1 t1 → R1 t1 t2 → Pre2 t2) → R1 ∘ R2 ⊆ R3 →
  GRealize sig (M1 · M2) Pre1 R3.
#sig #M1 #M2 #Pre1 #Pre2 #R1 #R2 #R3 #HR1 #HR2 #Hinv #Hsub
#t #HPre1 cases (sem_seq_guarded … HR1 HR2 Hinv t HPre1)
#k * #outc * #Hloop #Houtc @(ex_intro … k) @(ex_intro … outc)
% [@Hloop |@Hsub @Houtc]
qed.

theorem acc_sem_seq : ∀sig.∀M1,M2:TM sig.∀R1,Rtrue,Rfalse,acc.
  M1 ⊨ R1 → M2 ⊨ [ acc: Rtrue, Rfalse ] → 
  M1 · M2 ⊨ [ inr … acc: R1 ∘ Rtrue, R1 ∘ Rfalse ].
#sig #M1 #M2 #R1 #Rtrue #Rfalse #acc #HR1 #HR2 #t 
cases (HR1 t) #k1 * #outc1 * #Hloop1 #HM1
cases (HR2 (ctape sig (states ? M1) outc1)) #k2 * #outc2 * * #Hloop2 
#HMtrue #HMfalse
@(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … outc2))
% [ %
[@(loop_merge …
   (loop_lift ??? (lift_confL sig (states sig M1) (states sig M2))
   (step sig M1) (step sig (seq sig M1 M2)) 
   (λc.halt sig M1 (cstate … c)) 
   (λc.halt_liftL ?? (halt sig M1) (cstate … c)) … Hloop1))
  [ * *
   [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
   | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
  || #c0 #Hhalt <step_seq_liftL //
  | #x <p_halt_liftL %
  |6:cases outc1 #s1 #t1 %
  |7:@(loop_lift … (initc ?? (ctape … outc1)) … Hloop2) 
    [ * #s2 #t2 %
    | #c0 #Hhalt <step_seq_liftR // ]
  |whd in ⊢ (??(???%)?);whd in ⊢ (??%?);
   generalize in match Hloop1; cases outc1 #sc1 #tc1 #Hloop10 
   >(trans_liftL_true sig M1 M2 ??) 
    [ whd in ⊢ (??%?); whd in ⊢ (???%); //
    | @(loop_Some ?????? Hloop10) ]
 ]
| >(config_expand … outc2) in ⊢ (%→?); whd in ⊢ (??%?→?); 
  #Hqtrue destruct (Hqtrue)
  @(ex_intro … (ctape ? (FinSum (states ? M1) (states ? M2)) (lift_confL … outc1)))
  % // >eq_ctape_lift_conf_L >eq_ctape_lift_conf_R /2/ ]
| >(config_expand … outc2) in ⊢ (%→?); whd in ⊢ (?(??%?)→?); #Hqfalse
  @(ex_intro … (ctape ? (FinSum (states ? M1) (states ? M2)) (lift_confL … outc1)))
  % // >eq_ctape_lift_conf_L >eq_ctape_lift_conf_R @HMfalse
  @(not_to_not … Hqfalse) //
]
qed.

lemma acc_sem_seq_app : ∀sig.∀M1,M2:TM sig.∀R1,Rtrue,Rfalse,R2,R3,acc.
  M1 ⊨ R1 → M2 ⊨ [acc: Rtrue, Rfalse] → 
    (∀t1,t2,t3. R1 t1 t3 → Rtrue t3 t2 → R2 t1 t2) → 
    (∀t1,t2,t3. R1 t1 t3 → Rfalse t3 t2 → R3 t1 t2) → 
    M1 · M2 ⊨ [inr … acc : R2, R3].    
#sig #M1 #M2 #R1 #Rtrue #Rfalse #R2 #R3 #acc
#HR1 #HRacc #Hsub1 #Hsub2 
#t cases (acc_sem_seq … HR1 HRacc t)
#k * #outc * * #Hloop #Houtc1 #Houtc2 @(ex_intro … k) @(ex_intro … outc)
% [% [@Hloop
     |#H cases (Houtc1 H) #t3 * #Hleft #Hright @Hsub1 // ]
  |#H cases (Houtc2 H) #t3 * #Hleft #Hright @Hsub2 // ]
qed.
