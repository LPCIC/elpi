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

include "basics/star.ma".

(* added from λδ *)

lemma TC_strap: ∀A. ∀R:relation A. ∀a1,a,a2.
                R a1 a → TC … R a a2 → TC … R a1 a2.
/3 width=3/ qed.

lemma TC_reflexive: ∀A,R. reflexive A R → reflexive A (TC … R).
/2 width=1/ qed.

lemma TC_star_ind: ∀A,R. reflexive A R → ∀a1. ∀P:predicate A.
                   P a1 → (∀a,a2. TC … R a1 a → R a a2 → P a → P a2) →
                   ∀a2. TC … R a1 a2 → P a2.
#A #R #H #a1 #P #Ha1 #IHa1 #a2 #Ha12 elim Ha12 -a2 /3 width=4/
qed-.

inductive TC_dx (A:Type[0]) (R:relation A): A → A → Prop ≝
  |inj_dx: ∀a,c. R a c → TC_dx A R a c
  |step_dx : ∀a,b,c. R a b → TC_dx A R b c → TC_dx A R a c.

lemma TC_dx_strap: ∀A. ∀R: relation A.
                   ∀a,b,c. TC_dx A R a b → R b c → TC_dx A R a c.
#A #R #a #b #c #Hab elim Hab -a -b /3 width=3/
qed.

lemma TC_to_TC_dx: ∀A. ∀R: relation A.
                   ∀a1,a2. TC … R a1 a2 → TC_dx … R a1 a2.
#A #R #a1 #a2 #Ha12 elim Ha12 -a2 /2 width=3/
qed.

lemma TC_dx_to_TC: ∀A. ∀R: relation A.
                   ∀a1,a2. TC_dx … R a1 a2 → TC … R a1 a2.
#A #R #a1 #a2 #Ha12 elim Ha12 -a1 -a2 /2 width=3/
qed.

fact TC_ind_dx_aux: ∀A,R,a2. ∀P:predicate A.
                    (∀a1. R a1 a2 → P a1) →
                    (∀a1,a. R a1 a → TC … R a a2 → P a → P a1) →
                    ∀a1,a. TC … R a1 a → a = a2 → P a1.
#A #R #a2 #P #H1 #H2 #a1 #a #Ha1
elim (TC_to_TC_dx ???? Ha1) -a1 -a
[ #a #c #Hac #H destruct /2 width=1/
| #a #b #c #Hab #Hbc #IH #H destruct /3 width=4/
]
qed-.

lemma TC_ind_dx: ∀A,R,a2. ∀P:predicate A.
                 (∀a1. R a1 a2 → P a1) →
                 (∀a1,a. R a1 a → TC … R a a2 → P a → P a1) →
                 ∀a1. TC … R a1 a2 → P a1.
#A #R #a2 #P #H1 #H2 #a1 #Ha12
@(TC_ind_dx_aux … H1 H2 … Ha12) //
qed-.

lemma TC_symmetric: ∀A,R. symmetric A R → symmetric A (TC … R).
#A #R #HR #x #y #H @(TC_ind_dx ??????? H) -x /3 width=1/ /3 width=3/
qed.

lemma TC_star_ind_dx: ∀A,R. reflexive A R →
                      ∀a2. ∀P:predicate A. P a2 →
                      (∀a1,a. R a1 a → TC … R a a2 → P a → P a1) →
                      ∀a1. TC … R a1 a2 → P a1.
#A #R #HR #a2 #P #Ha2 #H #a1 #Ha12
@(TC_ind_dx … P ? H … Ha12) /3 width=4/
qed-.

lemma TC_Conf3: ∀A,B,S,R. Conf3 A B S R → Conf3 A B S (TC … R).
#A #B #S #R #HSR #b #a1 #Ha1 #a2 #H elim H -a2 /2 width=3/
qed.

(* ************ confluence of star *****************)

lemma star_strip: ∀A,R. confluent A R →
                  ∀a0,a1. star … R a0 a1 → ∀a2. R a0 a2 →
                  ∃∃a. R a1 a & star … R a2 a.
#A #R #HR #a0 #a1 #H elim H -a1 /2 width=3/
#a #a1 #_ #Ha1 #IHa0 #a2 #Ha02
elim (IHa0 … Ha02) -a0 #a0 #Ha0 #Ha20
elim (HR … Ha1 … Ha0) -a /3 width=5/
qed-.

lemma star_confluent: ∀A,R. confluent A R → confluent A (star … R).
#A #R #HR #a0 #a1 #H elim H -a1 /2 width=3/
#a #a1 #_ #Ha1 #IHa0 #a2 #Ha02
elim (IHa0 … Ha02) -a0 #a0 #Ha0 #Ha20
elim (star_strip … HR … Ha0 … Ha1) -a /3 width=5/
qed-.

(* relations on unboxed pairs ***********************************************)

inductive bi_TC (A,B) (R:bi_relation A B) (a:A) (b:B): relation2 A B ≝
  |bi_inj : ∀c,d. R a b c d → bi_TC A B R a b c d
  |bi_step: ∀c,d,e,f. bi_TC A B R a b c d → R c d e f → bi_TC A B R a b e f.

lemma bi_TC_strap: ∀A,B. ∀R:bi_relation A B. ∀a1,a,a2,b1,b,b2.
                   R a1 b1 a b → bi_TC … R a b a2 b2 → bi_TC … R a1 b1 a2 b2.
#A #B #R #a1 #a #a2 #b1 #b #b2 #HR #H elim H -a2 -b2 /2 width=4/ /3 width=4/
qed.

lemma bi_TC_reflexive: ∀A,B,R. bi_reflexive A B R →
                       bi_reflexive … (bi_TC … R).
/2 width=1/ qed.

inductive bi_TC_dx (A,B) (R:bi_relation A B): bi_relation A B ≝
  |bi_inj_dx  : ∀a1,a2,b1,b2. R a1 b1 a2 b2 → bi_TC_dx A B R a1 b1 a2 b2
  |bi_step_dx : ∀a1,a,a2,b1,b,b2. R a1 b1 a b → bi_TC_dx A B R a b a2 b2 →
                bi_TC_dx A B R a1 b1 a2 b2.

lemma bi_TC_dx_strap: ∀A,B. ∀R: bi_relation A B.
                      ∀a1,a,a2,b1,b,b2. bi_TC_dx A B R a1 b1 a b →
                      R a b a2 b2 → bi_TC_dx A B R a1 b1 a2 b2.
#A #B #R #a1 #a #a2 #b1 #b #b2 #H1 elim H1 -a -b /3 width=4/
qed.

lemma bi_TC_to_bi_TC_dx: ∀A,B. ∀R: bi_relation A B.
                         ∀a1,a2,b1,b2. bi_TC … R a1 b1 a2 b2 →
                         bi_TC_dx … R a1 b1 a2 b2.
#A #B #R #a1 #a2 #b1 #b2 #H12 elim H12 -a2 -b2 /2 width=4/
qed.

lemma bi_TC_dx_to_bi_TC: ∀A,B. ∀R: bi_relation A B.
                         ∀a1,a2,b1,b2. bi_TC_dx … R a1 b1 a2 b2 →
                         bi_TC … R a1 b1 a2 b2.
#A #B #R #a1 #a2 #b1 #b2 #H12 elim H12 -a1 -a2 -b1 -b2 /2 width=4/
qed.

fact bi_TC_ind_dx_aux: ∀A,B,R,a2,b2. ∀P:relation2 A B.
                       (∀a1,b1. R a1 b1 a2 b2 → P a1 b1) →
                       (∀a1,a,b1,b. R a1 b1 a b → bi_TC … R a b a2 b2 → P a b → P a1 b1) →
                       ∀a1,a,b1,b. bi_TC … R a1 b1 a b → a = a2 → b = b2 → P a1 b1.
#A #B #R #a2 #b2 #P #H1 #H2 #a1 #a #b1 #b #H1
elim (bi_TC_to_bi_TC_dx … a1 a b1 b H1) -a1 -a -b1 -b
[ #a1 #x #b1 #y #H1 #Hx #Hy destruct /2 width=1/
| #a1 #a #x #b1 #b #y #H1 #H #IH #Hx #Hy destruct /3 width=5/
]
qed-.

lemma bi_TC_ind_dx: ∀A,B,R,a2,b2. ∀P:relation2 A B.
                    (∀a1,b1. R a1 b1 a2 b2 → P a1 b1) →
                    (∀a1,a,b1,b. R a1 b1 a b → bi_TC … R a b a2 b2 → P a b → P a1 b1) →
                    ∀a1,b1. bi_TC … R a1 b1 a2 b2 → P a1 b1.
#A #B #R #a2 #b2 #P #H1 #H2 #a1 #b1 #H12
@(bi_TC_ind_dx_aux ?????? H1 H2 … H12) //
qed-.

lemma bi_TC_symmetric: ∀A,B,R. bi_symmetric A B R →
                       bi_symmetric A B (bi_TC … R).
#A #B #R #HR #a1 #a2 #b1 #b2 #H21
@(bi_TC_ind_dx … a2 b2 H21) -a2 -b2 /3 width=1/ /3 width=4/
qed.

lemma bi_TC_transitive: ∀A,B,R. bi_transitive A B (bi_TC … R).
#A #B #R #a1 #a #b1 #b #H elim H -a -b /2 width=4/ /3 width=4/
qed.

definition bi_Conf3: ∀A,B,C. relation3 A B C → predicate (bi_relation A B) ≝
                     λA,B,C,S,R.
                     ∀c,a1,b1. S a1 b1 c → ∀a2,b2. R a1 b1 a2 b2 → S a2 b2 c.

lemma bi_TC_Conf3: ∀A,B,C,S,R. bi_Conf3 A B C S R → bi_Conf3 A B C S (bi_TC … R).
#A #B #C #S #R #HSR #c #a1 #b1 #Hab1 #a2 #b2 #H elim H -a2 -b2 /2 width=4/
qed.

lemma bi_TC_star_ind: ∀A,B,R. bi_reflexive A B R → ∀a1,b1. ∀P:relation2 A B.
                      P a1 b1 → (∀a,a2,b,b2. bi_TC … R a1 b1 a b → R a b a2 b2 → P a b → P a2 b2) →
                      ∀a2,b2. bi_TC … R a1 b1 a2 b2 → P a2 b2.
#A #B #R #HR #a1 #b1 #P #H1 #IH #a2 #b2 #H12 elim H12 -a2 -b2 /3 width=5/
qed-.

lemma bi_TC_star_ind_dx: ∀A,B,R. bi_reflexive A B R →
                         ∀a2,b2. ∀P:relation2 A B. P a2 b2 →
                         (∀a1,a,b1,b. R a1 b1 a b → bi_TC … R a b a2 b2 → P a b → P a1 b1) →
                         ∀a1,b1. bi_TC … R a1 b1 a2 b2 → P a1 b1.
#A #B #R #HR #a2 #b2 #P #H2 #IH #a1 #b1 #H12
@(bi_TC_ind_dx … IH … a1 b1 H12) /3 width=5/
qed-.

definition bi_star: ∀A,B,R. bi_relation A B ≝
                    λA,B,R. bi_RC A B (bi_TC … R).

lemma bi_star_bi_reflexive: ∀A,B,R. bi_reflexive A B (bi_star … R).
/2 width=1/ qed.

lemma bi_TC_to_bi_star: ∀A,B,R,a1,b1,a2,b2.
                        bi_TC A B R a1 b1 a2 b2 → bi_star A B R a1 b1 a2 b2.
/2 width=1/ qed.

lemma bi_R_to_bi_star: ∀A,B,R,a1,b1,a2,b2.
                       R a1 b1 a2 b2 → bi_star A B R a1 b1 a2 b2.
/3 width=1/ qed.

lemma bi_star_strap1: ∀A,B,R,a1,a,a2,b1,b,b2. bi_star A B R a1 b1 a b →
                      R a b a2 b2 → bi_star A B R a1 b1 a2 b2.
#A #B #R #a1 #a #a2 #b1 #b #b2 *
[ /3 width=4/
| * #H1 #H2 destruct /2 width=1/
]
qed.

lemma bi_star_strap2: ∀A,B,R,a1,a,a2,b1,b,b2. R a1 b1 a b →
                      bi_star A B R a b a2 b2 → bi_star A B R a1 b1 a2 b2.
#A #B #R #a1 #a #a2 #b1 #b #b2 #H *
[ /3 width=4/
| * #H1 #H2 destruct /2 width=1/
]
qed.

lemma bi_star_to_bi_TC_to_bi_TC: ∀A,B,R,a1,a,a2,b1,b,b2. bi_star A B R a1 b1 a b →
                                 bi_TC A B R a b a2 b2 → bi_TC A B R a1 b1 a2 b2.
#A #B #R #a1 #a #a2 #b1 #b #b2 *
[ /2 width=4/
| * #H1 #H2 destruct /2 width=1/
]
qed.

lemma bi_TC_to_bi_star_to_bi_TC: ∀A,B,R,a1,a,a2,b1,b,b2. bi_TC A B R a1 b1 a b →
                                 bi_star A B R a b a2 b2 → bi_TC A B R a1 b1 a2 b2.
#A #B #R #a1 #a #a2 #b1 #b #b2 #H *
[ /2 width=4/
| * #H1 #H2 destruct /2 width=1/
]
qed.

lemma bi_tansitive_bi_star: ∀A,B,R. bi_transitive A B (bi_star … R).
#A #B #R #a1 #a #b1 #b #H #a2 #b2 *
[ /3 width=4/
| * #H1 #H2 destruct /2 width=1/
]
qed.

lemma bi_star_ind: ∀A,B,R,a1,b1. ∀P:relation2 A B. P a1 b1 →
                   (∀a,a2,b,b2. bi_star … R a1 b1 a b → R a b a2 b2 → P a b → P a2 b2) →
                   ∀a2,b2. bi_star … R a1 b1 a2 b2 → P a2 b2.
#A #B #R #a1 #b1 #P #H #IH #a2 #b2 *
[ #H12 elim H12 -a2 -b2 /2 width=5/ -H /3 width=5/
| * #H1 #H2 destruct //
]
qed-.

lemma bi_star_ind_dx: ∀A,B,R,a2,b2. ∀P:relation2 A B. P a2 b2 →
                      (∀a1,a,b1,b. R a1 b1 a b → bi_star … R a b a2 b2 → P a b → P a1 b1) →
                      ∀a1,b1. bi_star … R a1 b1 a2 b2 → P a1 b1.
#A #B #R #a2 #b2 #P #H #IH #a1 #b1 *
[ #H12 @(bi_TC_ind_dx … a1 b1 H12) -a1 -b1 /2 width=5/ -H /3 width=5/
| * #H1 #H2 destruct //
]
qed-.

(* relations on unboxed triples *********************************************)

inductive tri_TC (A,B,C) (R:tri_relation A B C) (a1:A) (b1:B) (c1:C): relation3 A B C ≝
  |tri_inj : ∀a2,b2,c2. R a1 b1 c1 a2 b2 c2 → tri_TC A B C R a1 b1 c1 a2 b2 c2 
  |tri_step: ∀a,a2,b,b2,c,c2. 
             tri_TC A B C R a1 b1 c1 a b c → R a b c a2 b2 c2 →
             tri_TC A B C R a1 b1 c1 a2 b2 c2.

lemma tri_TC_strap: ∀A,B,C. ∀R:tri_relation A B C. ∀a1,a,a2,b1,b,b2,c1,c,c2.
                    R a1 b1 c1 a b c → tri_TC … R a b c a2 b2 c2 →
                    tri_TC … R a1 b1 c1 a2 b2 c2.
#A #B #C #R #a1 #a #a2 #b1 #b #b2 #c1 #c #c2 #HR #H elim H -a2 -b2 -c2 /2 width=5/ /3 width=5/
qed.

lemma tri_TC_reflexive: ∀A,B,C,R. tri_reflexive A B C R →
                        tri_reflexive … (tri_TC … R).
/2 width=1/ qed.

inductive tri_TC_dx (A,B,C) (R:tri_relation A B C): tri_relation A B C ≝
  |tri_inj_dx  : ∀a1,a2,b1,b2,c1,c2. R a1 b1 c1 a2 b2 c2 → tri_TC_dx A B C R a1 b1 c1 a2 b2 c2
  |tri_step_dx : ∀a1,a,a2,b1,b,b2,c1,c,c2.
                 R a1 b1 c1 a b c → tri_TC_dx A B C R a b c a2 b2 c2 →
                 tri_TC_dx A B C R a1 b1 c1 a2 b2 c2.

lemma tri_TC_dx_strap: ∀A,B,C. ∀R: tri_relation A B C.
                       ∀a1,a,a2,b1,b,b2,c1,c,c2.
                       tri_TC_dx A B C R a1 b1 c1 a b c →
                       R a b c a2 b2 c2 → tri_TC_dx A B C R a1 b1 c1 a2 b2 c2.
#A #B #C #R #a1 #a #a2 #b1 #b #b2 #c1 #c #c2 #H1 elim H1 -a -b -c /3 width=5/
qed.

lemma tri_TC_to_tri_TC_dx: ∀A,B,C. ∀R: tri_relation A B C.
                           ∀a1,a2,b1,b2,c1,c2. tri_TC … R a1 b1 c1 a2 b2 c2 →
                           tri_TC_dx … R a1 b1 c1 a2 b2 c2.
#A #B #C #R #a1 #a2 #b1 #b2 #c1 #c2 #H12 elim H12 -a2 -b2 -c2 /2 width=1/ /2 width=5/
qed.

lemma tri_TC_dx_to_tri_TC: ∀A,B,C. ∀R: tri_relation A B C.
                           ∀a1,a2,b1,b2,c1,c2. tri_TC_dx … R a1 b1 c1 a2 b2 c2 →
                           tri_TC … R a1 b1 c1 a2 b2 c2.
#A #B #C #R #a1 #a2 #b1 #b2 #c1 #c2 #H12 elim H12 -a1 -a2 -b1 -b2 -c1 -c2
/2 width=1/ /2 width=5/
qed.

fact tri_TC_ind_dx_aux: ∀A,B,C,R,a2,b2,c2. ∀P:relation3 A B C.
                        (∀a1,b1,c1. R a1 b1 c1 a2 b2 c2→ P a1 b1 c1) →
                        (∀a1,a,b1,b,c1,c. R a1 b1 c1 a b c → tri_TC … R a b c a2 b2 c2 → P a b c → P a1 b1 c1) →
                        ∀a1,a,b1,b,c1,c. tri_TC … R a1 b1 c1 a b c → a = a2 → b = b2 → c = c2 → P a1 b1 c1.
#A #B #C #R #a2 #b2 #c2 #P #H1 #H2 #a1 #a #b1 #b #c1 #c #H1
elim (tri_TC_to_tri_TC_dx … a1 a b1 b c1 c H1) -a1 -a -b1 -b -c1 -c
[ #a1 #x #b1 #y #c1 #z #H1 #Hx #Hy #Hz destruct /2 width=1/
| #a1 #a #x #b1 #b #y #c1 #c #z #H1 #H #IH #Hx #Hy #Hz destruct /3 width=6/
]
qed-.

lemma tri_TC_ind_dx: ∀A,B,C,R,a2,b2,c2. ∀P:relation3 A B C.
                     (∀a1,b1,c1. R a1 b1 c1 a2 b2 c2 → P a1 b1 c1) →
                     (∀a1,a,b1,b,c1,c. R a1 b1 c1 a b c → tri_TC … R a b c a2 b2 c2 → P a b c → P a1 b1 c1) →
                     ∀a1,b1,c1. tri_TC … R a1 b1 c1 a2 b2 c2 → P a1 b1 c1.
#A #B #C #R #a2 #b2 #c2 #P #H1 #H2 #a1 #b1 #c1 #H12
@(tri_TC_ind_dx_aux ???????? H1 H2 … H12) //
qed-.

lemma tri_TC_symmetric: ∀A,B,C,R. tri_symmetric A B C R →
                        tri_symmetric … (tri_TC … R).
#A #B #C #R #HR #a1 #a2 #b1 #b2 #c1 #c2 #H21
@(tri_TC_ind_dx … a2 b2 c2 H21) -a2 -b2 -c2 /3 width=1/ /3 width=5/
qed.

lemma tri_TC_transitive: ∀A,B,C,R. tri_transitive A B C (tri_TC … R).
#A #B #C #R #a1 #a #b1 #b #c1 #c #H elim H -a -b -c /2 width=5/ /3 width=5/
qed.

definition tri_Conf4: ∀A,B,C,D. relation4 A B C D → predicate (tri_relation A B C) ≝
                      λA,B,C,D,S,R.
                      ∀d,a1,b1,c1. S a1 b1 c1 d → ∀a2,b2,c2. R a1 b1 c1 a2 b2 c2 → S a2 b2 c2 d.

lemma tri_TC_Conf4: ∀A,B,C,D,S,R.
                    tri_Conf4 A B C D S R → tri_Conf4 A B C D S (tri_TC … R).
#A #B #C #D #S #R #HSR #d #a1 #b1 #c1 #Habc1 #a2 #b2 #c2 #H elim H -a2 -b2 -c2
/2 width=5/
qed.

lemma tri_TC_star_ind: ∀A,B,C,R. tri_reflexive A B C R →
                       ∀a1,b1,c1. ∀P:relation3 A B C.
                       P a1 b1 c1 → (∀a,a2,b,b2,c,c2. tri_TC … R a1 b1 c1 a b c → R a b c a2 b2 c2 → P a b c → P a2 b2 c2) →
                       ∀a2,b2,c2. tri_TC … R a1 b1 c1 a2 b2 c2 → P a2 b2 c2.
#A #B #C #R #HR #a1 #b1 #c1 #P #H1 #IH #a2 #b2 #c2 #H12 elim H12 -a2 -b2 -c2
/2 width=6/ /3 width=6/
qed-.

lemma tri_TC_star_ind_dx: ∀A,B,C,R. tri_reflexive A B C R →
                          ∀a2,b2,c2. ∀P:relation3 A B C. P a2 b2 c2 →
                          (∀a1,a,b1,b,c1,c. R a1 b1 c1 a b c → tri_TC … R a b c a2 b2 c2 → P a b c → P a1 b1 c1) →
                          ∀a1,b1,c1. tri_TC … R a1 b1 c1 a2 b2 c2 → P a1 b1 c1.
#A #B #C #R #HR #a2 #b2 #c2 #P #H2 #IH #a1 #b1 #c1 #H12
@(tri_TC_ind_dx  … IH … a1 b1 c1 H12) /3 width=6/
qed-.
