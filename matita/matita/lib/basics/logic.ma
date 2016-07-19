 (*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_______________________________________________________________ *)

include "basics/pts.ma".
include "hints_declaration.ma".

(* propositional equality *)

inductive eq (A:Type[2]) (x:A) : A → Prop ≝
    refl: eq A x x. 
    
interpretation "leibnitz's equality" 'eq t x y = (eq t x y).
interpretation "leibniz reflexivity" 'refl = refl.

lemma eq_rect_r:
 ∀A.∀a,x.∀p:eq ? x a.∀P: ∀x:A. eq ? x a → Type[3]. P a (refl A a) → P x p.
 #A #a #x #p (cases p) // qed.

lemma eq_ind_r :
 ∀A.∀a.∀P: ∀x:A. x = a → Prop. P a (refl A a) → ∀x.∀p:eq ? x a.P x p.
 #A #a #P #p #x0 #p0; @(eq_rect_r ? ? ? p0) //; qed.

lemma eq_rect_Type0_r:
  ∀A.∀a.∀P: ∀x:A. eq ? x a → Type[0]. P a (refl A a) → ∀x.∀p:eq ? x a.P x p.
  #A #a #P #H #x #p lapply H lapply P
  cases p; //; qed.

lemma eq_rect_Type1_r:
  ∀A.∀a.∀P: ∀x:A. eq ? x a → Type[1]. P a (refl A a) → ∀x.∀p:eq ? x a.P x p.
  #A #a #P #H #x #p lapply H lapply P
  cases p; //; qed.

lemma eq_rect_Type2_r:
  ∀A.∀a.∀P: ∀x:A. eq ? x a → Type[2]. P a (refl A a) → ∀x.∀p:eq ? x a.P x p.
  #A #a #P #H #x #p lapply H lapply P
  cases p; //; qed.

lemma eq_rect_Type3_r:
  ∀A.∀a.∀P: ∀x:A. eq ? x a → Type[3]. P a (refl A a) → ∀x.∀p:eq ? x a.P x p.
  #A #a #P #H #x #p lapply H lapply P
  cases p; //; qed.

theorem rewrite_l: ∀A:Type[2].∀x.∀P:A → Type[2]. P x → ∀y. x = y → P y.
#A #x #P #Hx #y #Heq (cases Heq); //; qed.

theorem sym_eq: ∀A.∀x,y:A. x = y → y = x.
#A #x #y #Heq @(rewrite_l A x (λz.z=x)) // qed.

theorem rewrite_r: ∀A:Type[2].∀x.∀P:A → Type[2]. P x → ∀y. y = x → P y.
#A #x #P #Hx #y #Heq (cases (sym_eq ? ? ? Heq)); //; qed.

theorem eq_coerc: ∀A,B:Type[0].A→(A=B)→B.
#A #B #Ha #Heq (elim Heq); //; qed.

theorem trans_eq : ∀A.∀x,y,z:A. x = y → y = z → x = z.
#A #x #y #z #H1 #H2 >H1; //; qed.

theorem eq_f: ∀A,B.∀f:A→B.∀x,y:A. x=y → f x = f y.
#A #B #f #x #y #H >H; //; qed.

(* deleterio per auto? *)
theorem eq_f2: ∀A,B,C.∀f:A→B→C.
∀x1,x2:A.∀y1,y2:B. x1=x2 → y1=y2 → f x1 y1 = f x2 y2.
#A #B #C #f #x1 #x2 #y1 #y2 #E1 #E2 >E1; >E2; //; qed. 

lemma eq_f3: ∀A,B,C,D.∀f:A→B→C->D.
∀x1,x2:A.∀y1,y2:B. ∀z1,z2:C. x1=x2 → y1=y2 → z1=z2 → f x1 y1 z1 = f x2 y2 z2.
#A #B #C #D #f #x1 #x2 #y1 #y2 #z1 #z2 #E1 #E2 #E3 >E1; >E2; >E3 //; qed.

(* hint to genereric equality 
definition eq_equality: equality ≝
 mk_equality eq refl rewrite_l rewrite_r.


unification hint 0 ≔ T,a,b;
 X ≟ eq_equality
(*------------------------------------*) ⊢
    equal X T a b ≡ eq T a b.
*)
  
(********** connectives ********)

inductive True: Prop ≝  
I : True.

inductive False: Prop ≝ .

(* ndefinition Not: Prop → Prop ≝
λA. A → False. *)

inductive Not (A:Prop): Prop ≝
nmk: (A → False) → Not A.

interpretation "logical not" 'not x = (Not x).

theorem absurd : ∀A:Prop. A → ¬A → False.
#A #H #Hn (elim Hn); /2/; qed.

(*
ntheorem absurd : ∀ A,C:Prop. A → ¬A → C.
#A; #C; #H; #Hn; nelim (Hn H).
nqed. *)

theorem not_to_not : ∀A,B:Prop. (A → B) → ¬B →¬A.
/4/; qed.

(* inequality *)
interpretation "leibnitz's non-equality" 'neq t x y = (Not (eq t x y)).

theorem sym_not_eq: ∀A.∀x,y:A. x ≠ y → y ≠ x.
/3/; qed.

(* and *)
inductive And (A,B:Prop) : Prop ≝
    conj : A → B → And A B.

interpretation "logical and" 'and x y = (And x y).

theorem proj1: ∀A,B:Prop. A ∧ B → A.
#A #B #AB (elim AB) //; qed.

theorem proj2: ∀ A,B:Prop. A ∧ B → B.
#A #B #AB (elim AB) //; qed.

(* or *)
inductive Or (A,B:Prop) : Prop ≝
     or_introl : A → (Or A B)
   | or_intror : B → (Or A B).

interpretation "logical or" 'or x y = (Or x y).

definition decidable : Prop → Prop ≝ 
λ A:Prop. A ∨ ¬ A.

(* exists *)
inductive ex (A:Type[0]) (P:A → Prop) : Prop ≝
    ex_intro: ∀ x:A. P x →  ex A P.
    
interpretation "exists" 'exists x = (ex ? x).

inductive ex2 (A:Type[0]) (P,Q:A →Prop) : Prop ≝
    ex2_intro: ∀ x:A. P x → Q x → ex2 A P Q.

interpretation "exists on two predicates" 'exists2 x1 x2 = (ex2 ? x1 x2).

lemma ex2_commute: ∀A0. ∀P0,P1:A0→Prop. (∃∃x0. P0 x0 & P1 x0) → ∃∃x0. P1 x0 & P0 x0.
#A0 #P0 #P1 * /2 width=3/
qed-.

(* iff *)
definition iff :=
 λ A,B. (A → B) ∧ (B → A).

interpretation "iff" 'iff a b = (iff a b).

lemma iff_sym: ∀A,B. A ↔ B → B ↔ A.
#A #B * /3/ qed.

lemma iff_trans:∀A,B,C. A ↔ B → B ↔ C → A ↔ C.
#A #B #C * #H1 #H2 * #H3 #H4 % /3/ qed.

lemma iff_not: ∀A,B. A ↔ B → ¬A ↔ ¬B.
#A #B * #H1 #H2 % /3/ qed.

lemma iff_and_l: ∀A,B,C. A ↔ B → C ∧ A ↔ C ∧ B.
#A #B #C * #H1 #H2 % * /3/ qed.  

lemma iff_and_r: ∀A,B,C. A ↔ B → A ∧ C ↔ B ∧ C.
#A #B #C * #H1 #H2 % * /3/ qed.  

lemma iff_or_l: ∀A,B,C. A ↔ B → C ∨ A ↔ C ∨ B.
#A #B #C * #H1 #H2 % * /3/ qed.  

lemma iff_or_r: ∀A,B,C. A ↔ B → A ∨ C ↔ B ∨ C.
#A #B #C * #H1 #H2 % * /3/ qed.  

(* cose per destruct: da rivedere *) 

definition R0 ≝ λT:Type[0].λt:T.t.
  
definition R1 ≝ eq_rect_Type0.

(* used for lambda-delta *)
definition R2 :
  ∀T0:Type[0].
  ∀a0:T0.
  ∀T1:∀x0:T0. a0=x0 → Type[0].
  ∀a1:T1 a0 (refl ? a0).
  ∀T2:∀x0:T0. ∀p0:a0=x0. ∀x1:T1 x0 p0. R1 ?? T1 a1 ? p0 = x1 → Type[0].
  ∀a2:T2 a0 (refl ? a0) a1 (refl ? a1).
  ∀b0:T0.
  ∀e0:a0 = b0.
  ∀b1: T1 b0 e0.
  ∀e1:R1 ?? T1 a1 ? e0 = b1.
  T2 b0 e0 b1 e1.
#T0 #a0 #T1 #a1 #T2 #a2 #b0 #e0 #b1 #e1 
@(eq_rect_Type0 ????? e1) 
@(R1 ?? ? ?? e0) 
@a2 
qed.

definition R3 :
  ∀T0:Type[0].
  ∀a0:T0.
  ∀T1:∀x0:T0. a0=x0 → Type[0].
  ∀a1:T1 a0 (refl ? a0).
  ∀T2:∀x0:T0. ∀p0:a0=x0. ∀x1:T1 x0 p0. R1 ?? T1 a1 ? p0 = x1 → Type[0].
  ∀a2:T2 a0 (refl ? a0) a1 (refl ? a1).
  ∀T3:∀x0:T0. ∀p0:a0=x0. ∀x1:T1 x0 p0.∀p1:R1 ?? T1 a1 ? p0 = x1.
      ∀x2:T2 x0 p0 x1 p1.R2 ???? T2 a2 x0 p0 ? p1 = x2 → Type[0].
  ∀a3:T3 a0 (refl ? a0) a1 (refl ? a1) a2 (refl ? a2).
  ∀b0:T0.
  ∀e0:a0 = b0.
  ∀b1: T1 b0 e0.
  ∀e1:R1 ?? T1 a1 ? e0 = b1.
  ∀b2: T2 b0 e0 b1 e1.
  ∀e2:R2 ???? T2 a2 b0 e0 ? e1 = b2.
  T3 b0 e0 b1 e1 b2 e2.
#T0 #a0 #T1 #a1 #T2 #a2 #T3 #a3 #b0 #e0 #b1 #e1 #b2 #e2 
@(eq_rect_Type0 ????? e2) 
@(R2 ?? ? ???? e0 ? e1) 
@a3 
qed.

definition R4 :
  ∀T0:Type[0].
  ∀a0:T0.
  ∀T1:∀x0:T0. eq T0 a0 x0 → Type[0].
  ∀a1:T1 a0 (refl T0 a0).
  ∀T2:∀x0:T0. ∀p0:eq (T0 …) a0 x0. ∀x1:T1 x0 p0.eq (T1 …) (R1 T0 a0 T1 a1 x0 p0) x1 → Type[0].
  ∀a2:T2 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1).
  ∀T3:∀x0:T0. ∀p0:eq (T0 …) a0 x0. ∀x1:T1 x0 p0.∀p1:eq (T1 …) (R1 T0 a0 T1 a1 x0 p0) x1.
      ∀x2:T2 x0 p0 x1 p1.eq (T2 …) (R2 T0 a0 T1 a1 T2 a2 x0 p0 x1 p1) x2 → Type[0].
  ∀a3:T3 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1) 
      a2 (refl (T2 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1)) a2). 
  ∀T4:∀x0:T0. ∀p0:eq (T0 …) a0 x0. ∀x1:T1 x0 p0.∀p1:eq (T1 …) (R1 T0 a0 T1 a1 x0 p0) x1.
      ∀x2:T2 x0 p0 x1 p1.∀p2:eq (T2 …) (R2 T0 a0 T1 a1 T2 a2 x0 p0 x1 p1) x2.
      ∀x3:T3 x0 p0 x1 p1 x2 p2.∀p3:eq (T3 …) (R3 T0 a0 T1 a1 T2 a2 T3 a3 x0 p0 x1 p1 x2 p2) x3. 
      Type[0].
  ∀a4:T4 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1) 
      a2 (refl (T2 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1)) a2) 
      a3 (refl (T3 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1) 
                   a2 (refl (T2 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1)) a2))
                   a3).
  ∀b0:T0.
  ∀e0:eq (T0 …) a0 b0.
  ∀b1: T1 b0 e0.
  ∀e1:eq (T1 …) (R1 T0 a0 T1 a1 b0 e0) b1.
  ∀b2: T2 b0 e0 b1 e1.
  ∀e2:eq (T2 …) (R2 T0 a0 T1 a1 T2 a2 b0 e0 b1 e1) b2.
  ∀b3: T3 b0 e0 b1 e1 b2 e2.
  ∀e3:eq (T3 …) (R3 T0 a0 T1 a1 T2 a2 T3 a3 b0 e0 b1 e1 b2 e2) b3.
  T4 b0 e0 b1 e1 b2 e2 b3 e3.
#T0 #a0 #T1 #a1 #T2 #a2 #T3 #a3 #T4 #a4 #b0 #e0 #b1 #e1 #b2 #e2 #b3 #e3 
@(eq_rect_Type0 ????? e3) 
@(R3 ????????? e0 ? e1 ? e2) 
@a4 
qed.

definition eqProp ≝ λA:Prop.eq A.

(* Example to avoid indexing and the consequential creation of ill typed
   terms during paramodulation *)
lemma lemmaK : ∀A.∀x:A.∀h:x=x. eqProp ? h (refl A x).
#A #x #h @(refl ? h: eqProp ? ? ?).
qed-.

theorem streicherK : ∀T:Type[2].∀t:T.∀P:t = t → Type[3].P (refl ? t) → ∀p.P p.
 #T #t #P #H #p >(lemmaK T t p) @H
qed-.
