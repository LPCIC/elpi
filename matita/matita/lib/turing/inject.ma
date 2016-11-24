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
(* include "turing/basic_machines.ma". *)

(******************* inject a mono machine into a multi tape one **********************)

definition inject_trans ≝ λsig,states:FinSet.λn,i:nat.
  λtrans:states × (option sig) → states  × (option sig × move).
  λp:states × (Vector (option sig) (S n)).
  let 〈q,a〉 ≝ p in
  let 〈nq,na〉 ≝ trans 〈q,nth i ? a (None ?)〉 in
  〈nq, change_vec ? (S n) (null_action ? n) na i〉.

definition inject_TM ≝ λsig.λM:TM sig.λn,i.
  mk_mTM sig n
    (states ? M)
    (inject_trans sig (states ? M) n i ?) (* (trans sig M))*)
    (start ? M)
    (halt ? M).
(* ????? *)
lapply (trans sig M)  #trans #x lapply (trans x) * *
#s #a #m % [ @s | % [ @a | @m ] ]
qed.

lemma current_chars_change_vec: ∀sig,n,v,a,i. i < S n →
   current_chars sig ? (change_vec ? (S n) v a i) =
   change_vec ? (S n)(current_chars ?? v) (current ? a) i.
#sig #n #v #a #i #Hi @(eq_vec … (None ?)) #i0 #Hi0
change with (vec_map ?????) in match (current_chars ???);
<(nth_vec_map … (niltape ?))
cases (decidable_eq_nat i i0) #Hii0
[ >Hii0 >nth_change_vec // >nth_change_vec //
| >nth_change_vec_neq // >nth_change_vec_neq // @nth_vec_map ]
qed.

lemma inject_trans_def :∀sig:FinSet.∀n,i:nat.i < S n → 
  ∀M,v,s,a,sn,an,mn.
  trans sig M 〈s,a〉 = 〈sn,an,mn〉 → 
  cic:/matita/turing/turing/trans#fix:0:2:9 sig n (inject_TM sig M n i) 〈s,change_vec ? (S n) v a i〉 = 
    〈sn,change_vec ? (S n) (null_action ? n) 〈an,mn〉 i〉.
#sig #n #i #Hlt #M #v #s #a #sn #an #mn #Htrans
whd in ⊢ (??%?); >nth_change_vec // >Htrans //
qed.

lemma inj_ter: ∀A,B,C.∀p:A×B×C. 
  p = 〈\fst (\fst p), \snd (\fst p), \snd p〉.
// qed.

lemma inject_step : ∀sig,n,M,i,q,t,nq,nt,v. i < S n →
  step sig M (mk_config ?? q t) = mk_config ?? nq nt → 
  cic:/matita/turing/turing/step#def:12 sig n (inject_TM sig M n i) 
    (mk_mconfig ?? n q (change_vec ? (S n) v t i)) 
  = mk_mconfig ?? n nq (change_vec ? (S n) v nt i).
#sig #n #M #i #q #t #nq #nt #v #lein whd in ⊢ (??%?→?);
whd in match (step ????); >(current_chars_change_vec … lein)
>(inj_ter … (trans sig M ?)) whd in ⊢ (??%?→?); #H
>(inject_trans_def sig n i lein M …) 
[|>(eq_pair_fst_snd ?? (trans sig M 〈q,current sig t〉))
  >(eq_pair_fst_snd ?? (\fst (trans sig M 〈q,current sig t〉))) %
| *: skip ]
whd in ⊢ (??%?); @eq_f2 [destruct (H) // ]
@(eq_vec … (niltape ?)) #i0 #lei0n
cases (decidable_eq_nat … i i0) #Hii0
[ >Hii0 >nth_change_vec // >tape_move_multi_def >pmap_change >nth_change_vec // destruct (H) //
| >nth_change_vec_neq // >tape_move_multi_def  >pmap_change >nth_change_vec_neq //
  <tape_move_multi_def >tape_move_null_action //
]
qed. 

lemma halt_inject: ∀sig,n,M,i,x.
  cic:/matita/turing/turing/halt#fix:0:2:9 sig n (inject_TM sig M n i) x
   = halt sig M x.
// qed.

lemma de_option: ∀A,a,b. Some A a = Some A b → a = b. 
#A #a #b #H destruct //
qed. 

lemma loop_inject: ∀sig,n,M,i,k,ins,int,outs,outt,vt.i < S n → 
 loopM sig M k (mk_config ?? ins int) = Some ? (mk_config ?? outs outt) → 
 cic:/matita/turing/turing/loopM#def:13 sig n (inject_TM sig M n i) k (mk_mconfig ?? n ins (change_vec ?? vt int i))
  =Some ? (mk_mconfig sig ? n outs (change_vec ?? vt outt i)).
#sig #n #M #i #k elim k -k
  [#ins #int #outs #outt #vt #Hin normalize in ⊢ (%→?); #H destruct
  |#k #Hind #ins #int #outs #outt #vt #Hin whd in ⊢ (??%?→??%?);
   >halt_inject whd in match (cstate ????);
   cases (true_or_false (halt sig M ins)) #Hhalt >Hhalt 
   whd in ⊢ (??%?→??%?);
    [#H @eq_f whd in ⊢ (??%?); lapply (de_option ??? H) -H 
     whd  in ⊢ (??%?→?); #H @eq_f2  
      [whd in ⊢ (??%?); destruct (H) //
      |@(eq_vec … (niltape ?)) #j #lejn
       cases (true_or_false (eqb i j)) #eqij
        [>(eqb_true_to_eq … eqij) >nth_change_vec //
         destruct (H) >nth_change_vec //
        |destruct (H) //
        ]
      ]
    |>(config_expand … (step ???)) #H <(Hind … H) // 
     >loopM_unfold @eq_f >inject_step //
    ]
  ]
qed.

definition inject_R ≝ λsig.λR:relation (tape sig).λn,i:nat.
  λv1,v2: (Vector (tape sig) (S n)).
  R (nth i ? v1 (niltape ?)) (nth i ? v2 (niltape ?)) ∧
  ∀j. i ≠ j → nth j ? v1 (niltape ?) = nth j ? v2 (niltape ?). 

theorem sem_inject: ∀sig.∀M:TM sig.∀R.∀n,i.
 i≤n → M ⊨ R → inject_TM sig M n i ⊨ inject_R sig R n i. 
#sig #M #R #n #i #lein #HR #vt cases (HR (nth i ? vt (niltape ?)))
#k * * #outs #outt * #Hloop #HRout @(ex_intro ?? k) 
@(ex_intro ?? (mk_mconfig ?? n outs (change_vec ? (S n) vt outt i))) %
  [whd in ⊢ (??(?????%)?); <(change_vec_same ?? vt i (niltape ?)) in ⊢ (??%?);
   @loop_inject /2 by refl, trans_eq, le_S_S/
  |%[>nth_change_vec // @le_S_S //
    |#j #i >nth_change_vec_neq //
    ]
  ]
qed.

theorem acc_sem_inject: ∀sig.∀M:TM sig.∀Rtrue,Rfalse,acc.∀n,i.
 i≤n → M ⊨ [ acc : Rtrue, Rfalse ] → 
 inject_TM sig M n i ⊨ [ acc : inject_R sig Rtrue n i, inject_R sig Rfalse n i ]. 
#sig #M #Rtrue #Rfalse #acc #n #i #lein #HR #vt cases (HR (nth i ? vt (niltape ?)))
#k * * #outs #outt * * #Hloop #HRtrue #HRfalse @(ex_intro ?? k) 
@(ex_intro ?? (mk_mconfig ?? n outs (change_vec ? (S n) vt outt i))) % [ %
  [whd in ⊢ (??(?????%)?); <(change_vec_same ?? vt i (niltape ?)) in ⊢ (??%?);
   @loop_inject /2 by refl, trans_eq, le_S_S/
  |#Hqtrue %
    [>nth_change_vec /2 by le_S_S/
    |#j #Hneq >nth_change_vec_neq //
    ] ]
  |#Hqfalse %
    [>nth_change_vec /2 by le_S_S/ @HRfalse @Hqfalse
    |#j #Hneq >nth_change_vec_neq //
    ] ]
qed.