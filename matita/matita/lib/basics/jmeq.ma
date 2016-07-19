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

include "basics/logic.ma".

inductive Sigma: Type[2] ≝
 mk_Sigma: ∀p1: Type[1]. p1 → Sigma.

definition p1: Sigma → Type[1].
 #S cases S #Y #_ @Y
qed.

definition p2: ∀S:Sigma. p1 S.
 #S cases S #Y #x @x
qed.

inductive jmeq (A:Type[1]) (x:A) : ∀B:Type[1]. B →Prop ≝
refl_jmeq : jmeq A x A x.

notation < "hvbox(term 46 a break maction (≃) (≃\sub(t,u)) term 46 b)"
  non associative with precedence 45
for @{ 'jmsimeq $t $a $u $b }.

notation > "hvbox(n break ≃ m)"
  non associative with precedence 45
for @{ 'jmsimeq ? $n ? $m }.

interpretation "john major's equality" 'jmsimeq t x u y = (jmeq t x u y).
interpretation "john major's reflexivity" 'refl = refl_jmeq.

definition eqProp ≝ λA:Prop.eq A.

lemma K : ∀A.∀x:A.∀h:x=x. eqProp ? h (refl A x).
#A #x #h @(refl ? h: eqProp ? ? ?).
qed.

definition cast:
 ∀A,B:Type[1].∀E:A=B. A → B.
 #A #B #E cases E #X @X
qed.

lemma tech1:
 ∀Aa,Bb:Sigma.∀E:Aa=Bb.
  cast (p1 Aa) (p1 Bb) ? (p2 Aa) = p2 Bb.
 [2: >E %
 | #Aa #Bb #E >E cases Bb #B #b normalize % ]
qed.
 
lemma gral: ∀A.∀x,y:A.
 mk_Sigma A x = mk_Sigma A y → x=y.
 #A #x #y #E lapply (tech1 ?? E)
 generalize in ⊢ (??(???%?)? → ?); #E1
 normalize in E1; >(K ?? E1) normalize
 #H @H
qed.

lemma jm_to_eq_sigma:
 ∀A,x,y. jmeq A x A y → mk_Sigma A x = mk_Sigma A y.
 #A #x #y #E cases E in ⊢ (???%); %
qed.

definition curry:
 ∀A,x.
  (∀y. jmeq A x A y → Type[0]) →
   (∀y. mk_Sigma A x = mk_Sigma A y → Type[0]).
 #A #x #f #y #E @(f y) >(gral ??? E) %
qed.

lemma G : ∀A.∀x:A.∀P:∀y:A.mk_Sigma A x = mk_Sigma A y →Type[0].
 P x (refl ? (mk_Sigma A x)) → ∀y.∀h:mk_Sigma A x = mk_Sigma A y.
  P y h.
 #A #x #P #H #y #E lapply (gral ??? E) #G generalize in match E;
 @(match G
    return λy.λ_. ∀e:mk_Sigma A x = mk_Sigma A y. P y e
   with
    [refl ⇒ ?])
 #E <(sym_eq ??? (K ?? E)) @H
qed.

definition PP: ∀A:Prop.∀P:A → Type[0]. A → Type[0].
 #A #P #a @(P a)
qed.

lemma E : ∀A.∀x:A.∀P:∀y:A.jmeq A x A y→Type[0].
 PP ? (P x) (refl_jmeq A x) → ∀y.∀h:jmeq A x A y.PP ? (P y) h.
 #A #a #P #H #b #E letin F ≝ (jm_to_eq_sigma ??? E)
 lapply (G ?? (curry ?? P) ?? F)
  [ normalize //
  | #H whd in H; @(H : PP ? (P b) ?) ]
qed.

lemma jmeq_elim : ∀A.∀x:A.∀P:∀y:A.jmeq A x A y→Type[0].
 P x (refl_jmeq A x) → ∀y.∀h:jmeq A x A y.P y h ≝ E.

lemma jmeq_to_eq: ∀A:Type[1]. ∀x,y:A. x≃y → x=y.
 #A #x #y #JMEQ @(jmeq_elim ? x … JMEQ) %
qed.

coercion jmeq_to_eq: ∀A:Type[1]. ∀x,y:A. ∀p:x≃y.x=y ≝ jmeq_to_eq on _p:?≃? to ?=?.

lemma eq_to_jmeq:
  ∀A: Type[1].
  ∀x, y: A.
    x = y → x ≃ y.
  //
qed.
