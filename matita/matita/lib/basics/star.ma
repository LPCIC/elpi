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

include "basics/relations.ma".

(* transitive closcure (plus) *)

inductive TC (A:Type[0]) (R:relation A) (a:A): A → Prop ≝
  |inj: ∀c. R a c → TC A R a c
  |step : ∀b,c.TC A R a b → R b c → TC A R a c.

theorem trans_TC: ∀A,R,a,b,c. 
  TC A R a b → TC A R b c → TC A R a c.
#A #R #a #b #c #Hab #Hbc (elim Hbc) /2/
qed.

theorem TC_idem: ∀A,R. exteqR … (TC A R) (TC A (TC A R)).
#A #R #a #b % /2/ #H (elim H) /2/
qed.

lemma monotonic_TC: ∀A,R,S. subR A R S → subR A (TC A R) (TC A S).
#A #R #S #subRS #a #b #H (elim H) /3/
qed.

lemma sub_TC: ∀A,R,S. subR A R (TC A S) → subR A (TC A R) (TC A S).
#A #R #S #Hsub #a #b #H (elim H) /3/
qed.

theorem sub_TC_to_eq: ∀A,R,S. subR A R S → subR A S (TC A R) → 
  exteqR … (TC A R) (TC A S).
#A #R #S #sub1 #sub2 #a #b % /2/
qed.

theorem TC_inv: ∀A,R. exteqR ?? (TC A (inv A R)) (inv A (TC A R)).
#A #R #a #b %
#H (elim H) /2/ normalize #c #d #H1 #H2 #H3 @(trans_TC … H3) /2/
qed.
  
(* star *)
inductive star (A:Type[0]) (R:relation A) (a:A): A → Prop ≝
  |sstep: ∀b,c.star A R a b → R b c → star A R a c
  |srefl: star A R a a.

lemma R_to_star: ∀A,R,a,b. R a b → star A R a b.
#A #R #a #b /2/
qed.

theorem trans_star: ∀A,R,a,b,c. 
  star A R a b → star A R b c → star A R a c.
#A #R #a #b #c #Hab #Hbc (elim Hbc) /2/
qed.

theorem star_star: ∀A,R. exteqR … (star A R) (star A (star A R)).
#A #R #a #b % /2/ #H (elim H) /2/
qed.

lemma monotonic_star: ∀A,R,S. subR A R S → subR A (star A R) (star A S).
#A #R #S #subRS #a #b #H (elim H) /3/
qed.

lemma sub_star: ∀A,R,S. subR A R (star A S) → 
  subR A (star A R) (star A S).
#A #R #S #Hsub #a #b #H (elim H) /3/
qed.

theorem sub_star_to_eq: ∀A,R,S. subR A R S → subR A S (star A R) → 
  exteqR … (star A R) (star A S).
#A #R #S #sub1 #sub2 #a #b % /2/
qed.

theorem star_inv: ∀A,R. 
  exteqR ?? (star A (inv A R)) (inv A (star A R)).
#A #R #a #b %
#H (elim H) /2/ normalize #c #d #H1 #H2 #H3 @(trans_star … H3) /2/
qed.

lemma star_decomp_l : 
  ∀A,R,x,y.star A R x y → x = y ∨ ∃z.R x z ∧ star A R z y.
#A #R #x #y #Hstar elim Hstar
[ #b #c #Hleft #Hright *
  [ #H1 %2 @(ex_intro ?? c) % //
  | * #x0 * #H1 #H2 %2 @(ex_intro ?? x0) % /2/ ]
| /2/ ]
qed.

(* right associative version of star *)
inductive starl (A:Type[0]) (R:relation A) : A → A → Prop ≝
  |sstepl: ∀a,b,c.R a b → starl A R b c → starl A R a c
  |refll: ∀a.starl A R a a.
 
lemma starl_comp : ∀A,R,a,b,c.
  starl A R a b → R b c → starl A R a c.
#A #R #a #b #c #Hstar elim Hstar 
  [#a1 #b1 #c1 #Rab #sbc #Hind #a1 @(sstepl … Rab) @Hind //
  |#a1 #Rac @(sstepl … Rac) //
  ]
qed.

lemma star_compl : ∀A,R,a,b,c.
  R a b → star A R b c → star A R a c.
#A #R #a #b #c #Rab #Hstar elim Hstar 
  [#b1 #c1 #sbb1 #Rb1c1 #Hind @(sstep … Rb1c1) @Hind
  |@(sstep … Rab) //
  ]
qed.

lemma star_to_starl: ∀A,R,a,b.star A R a b → starl A R a b.
#A #R #a #b #Hs elim Hs //
#d #c #sad #Rdc #sad @(starl_comp … Rdc) //
qed.

lemma starl_to_star: ∀A,R,a,b.starl A R a b → star A R a b.
#A #R #a #b #Hs elim Hs // -Hs -b -a
#a #b #c #Rab #sbc #sbc @(star_compl … Rab) //
qed.

fact star_ind_l_aux: ∀A,R,a2. ∀P:predicate A.
                     P a2 →
                     (∀a1,a. R a1 a → star … R a a2 → P a → P a1) →
                     ∀a1,a. star … R a1 a → a = a2 → P a1.
#A #R #a2 #P #H1 #H2 #a1 #a #Ha1
elim (star_to_starl ???? Ha1) -a1 -a
[ #a #b #c #Hab #Hbc #IH #H destruct /3 width=4/
| #a #H destruct /2 width=1/
]
qed-.

(* imporeved version of star_ind_l with "left_parameter" *)
lemma star_ind_l: ∀A,R,a2. ∀P:predicate A.
                  P a2 →
                  (∀a1,a. R a1 a → star … R a a2 → P a → P a1) →
                  ∀a1. star … R a1 a2 → P a1.
#A #R #a2 #P #H1 #H2 #a1 #Ha12
@(star_ind_l_aux … H1 H2 … Ha12) //
qed.

(* TC and star *)

lemma TC_to_star: ∀A,R,a,b.TC A R a b → star A R a b.
#R #A #a #b #TCH (elim TCH) /2/
qed.

lemma star_case: ∀A,R,a,b. star A R a b → a = b ∨ TC A R a b.
#A #R #a #b #H (elim H) /2/ #c #d #star_ac #Rcd * #H1 %2 /2/.
qed.

(* equiv -- smallest equivalence relation containing R *)

inductive equiv (A:Type[0]) (R:relation A) : A → A → Prop ≝
  |inje: ∀a,b,c.equiv A R a b → R b c → equiv A R a c
  |refle: ∀a,b.equiv A R a b
  |syme: ∀a,b.equiv A R a b → equiv A R b a.
  
theorem trans_equiv: ∀A,R,a,b,c. 
  equiv A R a b → equiv A R b c → equiv A R a c.
#A #R #a #b #c #Hab #Hbc (elim Hbc) /2/
qed.
 
theorem equiv_equiv: ∀A,R. exteqR … (equiv A R) (equiv A (equiv A R)).
#A #R #a #b % /2/  
qed.

lemma monotonic_equiv: ∀A,R,S. subR A R S → subR A (equiv A R) (equiv A S).
#A #R #S #subRS #a #b #H (elim H) /3/
qed.

lemma sub_equiv: ∀A,R,S. subR A R (equiv A S) → 
  subR A (equiv A R) (equiv A S).
#A #R #S #Hsub #a #b #H (elim H) /2/
qed.

theorem sub_equiv_to_eq: ∀A,R,S. subR A R S → subR A S (equiv A R) → 
  exteqR … (equiv A R) (equiv A S).
#A #R #S #sub1 #sub2 #a #b % /2/
qed.

(* well founded part of a relation *)

inductive WF (A:Type[0]) (R:relation A) : A → Prop ≝
  | wf : ∀b.(∀a. R a b → WF A R a) → WF A R b.

lemma WF_antimonotonic: ∀A,R,S. subR A R S → 
  ∀a. WF A S a → WF A R a.
#A #R #S #subRS #a #HWF (elim HWF) #b
#H #Hind % #c #Rcb @Hind @subRS //
qed.

