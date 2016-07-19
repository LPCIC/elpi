(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "formal_topology/cprop_connectives.ma".

inductive eq (A:Type[0]) (x:A) : A → CProp[0] ≝
    refl: eq A x x.

notation "hvbox(a break = \sub \ID b)" non associative with precedence 45
for @{ 'eqID $a $b }.

notation > "hvbox(a break =_\ID b)" non associative with precedence 45
for @{ 'eqID ? $a $b }.

interpretation "ID eq" 'eqID x y = (eq ? x y).

record equivalence_relation (A:Type[0]) : Type[1] ≝
 { eq_rel:2> A → A → CProp[0];
   refl: reflexive ? eq_rel;
   sym: symmetric ? eq_rel;
   trans: transitive ? eq_rel
 }.

record setoid : Type[1] ≝
 { carr:> Type[0];
   eq: equivalence_relation carr
 }.

record equivalence_relation1 (A:Type[1]) : Type[2] ≝
 { eq_rel1:2> A → A → CProp[1];
   refl1: reflexive1 ? eq_rel1;
   sym1: symmetric1 ? eq_rel1;
   trans1: transitive1 ? eq_rel1
 }.

record setoid1: Type[2] ≝
 { carr1:> Type[1];
   eq1: equivalence_relation1 carr1
 }.

definition setoid1_of_setoid: setoid → setoid1.
 #s
  @mk_setoid1
  [ @(carr s)
  | @mk_equivalence_relation1
    [ @(eq_rel s)
      @(eq s)
    | @(refl s)
    | @(sym s)
    | @(trans s)]]
qed.

coercion setoid1_of_setoid.
(*
prefer coercion Type_OF_setoid.
*)
record equivalence_relation2 (A:Type[2]) : Type[3] ≝
 { eq_rel2:2> A → A → CProp[2];
   refl2: reflexive2 ? eq_rel2;
   sym2: symmetric2 ? eq_rel2;
   trans2: transitive2 ? eq_rel2
 }.

record setoid2: Type[3] ≝
 { carr2:> Type[2];
   eq2: equivalence_relation2 carr2
 }.

definition setoid2_of_setoid1: setoid1 → setoid2.
 #s
  @mk_setoid2
  [ @(carr1 s)
  | @mk_equivalence_relation2
    [ @(eq_rel1 s)
      @(eq1 s)
    | @(refl1 s)
    | @(sym1 s)
    | @(trans1 s)]]
qed.

coercion setoid2_of_setoid1.
(*
prefer coercion Type_OF_setoid2. 
prefer coercion Type_OF_setoid. 
prefer coercion Type_OF_setoid1.
(* we prefer 0 < 1 < 2 *)
*)
record equivalence_relation3 (A:Type[3]) : Type[4] ≝
 { eq_rel3:2> A → A → CProp[3];
   refl3: reflexive3 ? eq_rel3;
   sym3: symmetric3 ? eq_rel3;
   trans3: transitive3 ? eq_rel3
 }.

record setoid3: Type[4] ≝
 { carr3:> Type[3];
   eq3: equivalence_relation3 carr3
 }.

interpretation "setoid3 eq" 'eq t x y = (eq_rel3 ? (eq3 t) x y).
interpretation "setoid2 eq" 'eq t x y = (eq_rel2 ? (eq2 t) x y).
interpretation "setoid1 eq" 'eq t x y = (eq_rel1 ? (eq1 t) x y).
interpretation "setoid eq" 'eq t x y = (eq_rel ? (eq t) x y).

notation > "hvbox(a break =_12 b)" non associative with precedence 45
for @{ eq_rel2 (carr2 (setoid2_of_setoid1 ?)) (eq2 (setoid2_of_setoid1 ?)) $a $b }.
notation > "hvbox(a break =_0 b)" non associative with precedence 45
for @{ eq_rel ? (eq ?) $a $b }.
notation > "hvbox(a break =_1 b)" non associative with precedence 45
for @{ eq_rel1 ? (eq1 ?) $a $b }.
notation > "hvbox(a break =_2 b)" non associative with precedence 45
for @{ eq_rel2 ? (eq2 ?) $a $b }.
notation > "hvbox(a break =_3 b)" non associative with precedence 45
for @{ eq_rel3 ? (eq3 ?) $a $b }.

interpretation "setoid3 symmetry" 'invert r = (sym3 ???? r).
interpretation "setoid2 symmetry" 'invert r = (sym2 ???? r).
interpretation "setoid1 symmetry" 'invert r = (sym1 ???? r).
interpretation "setoid symmetry" 'invert r = (sym ???? r).
notation ".= r" with precedence 55 for @{'trans $r}.
interpretation "trans3" 'trans r = (trans3 ????? r).
interpretation "trans2" 'trans r = (trans2 ????? r).
interpretation "trans1" 'trans r = (trans1 ????? r).
interpretation "trans" 'trans r = (trans ????? r).

record unary_morphism (A,B: setoid) : Type[0] ≝
 { fun1:(*1>*) A → B;
   prop1: ∀a,a'. eq ? a a' → eq ? (fun1 a) (fun1 a')
 }.

record unary_morphism1 (A,B: setoid1) : Type[1] ≝
 { fun11:1> A → B;
   prop11: ∀a,a'. eq1 ? a a' → eq1 ? (fun11 a) (fun11 a')
 }.

record unary_morphism2 (A,B: setoid2) : Type[2] ≝
 { fun12:1> A → B;
   prop12: ∀a,a'. eq2 ? a a' → eq2 ? (fun12 a) (fun12 a')
 }.

record unary_morphism3 (A,B: setoid3) : Type[3] ≝
 { fun13:1> A → B;
   prop13: ∀a,a'. eq3 ? a a' → eq3 ? (fun13 a) (fun13 a')
 }.

record binary_morphism (A,B,C:setoid) : Type[0] ≝
 { fun2:2> A → B → C;
   prop2: ∀a,a',b,b'. eq ? a a' → eq ? b b' → eq ? (fun2 a b) (fun2 a' b')
 }.

record binary_morphism1 (A,B,C:setoid1) : Type[1] ≝
 { fun21:2> A → B → C;
   prop21: ∀a,a',b,b'. eq1 ? a a' → eq1 ? b b' → eq1 ? (fun21 a b) (fun21 a' b')
 }.

record binary_morphism2 (A,B,C:setoid2) : Type[2] ≝
 { fun22:2> A → B → C;
   prop22: ∀a,a',b,b'. eq2 ? a a' → eq2 ? b b' → eq2 ? (fun22 a b) (fun22 a' b')
 }.

record binary_morphism3 (A,B,C:setoid3) : Type[3] ≝
 { fun23:2> A → B → C;
   prop23: ∀a,a',b,b'. eq3 ? a a' → eq3 ? b b' → eq3 ? (fun23 a b) (fun23 a' b')
 }.

notation "† c" with precedence 90 for @{'prop1 $c }.
notation "l ‡ r" with precedence 90 for @{'prop2 $l $r }.
notation "#" with precedence 90 for @{'refl}.
interpretation "prop1" 'prop1 c  = (prop1 ????? c).
interpretation "prop11" 'prop1 c = (prop11 ????? c).
interpretation "prop12" 'prop1 c = (prop12 ????? c).
interpretation "prop13" 'prop1 c = (prop13 ????? c).
interpretation "prop2" 'prop2 l r = (prop2 ???????? l r).
interpretation "prop21" 'prop2 l r = (prop21 ???????? l r).
interpretation "prop22" 'prop2 l r = (prop22 ???????? l r).
interpretation "prop23" 'prop2 l r = (prop23 ???????? l r).
interpretation "refl" 'refl = (refl ???).
interpretation "refl1" 'refl = (refl1 ???).
interpretation "refl2" 'refl = (refl2 ???).
interpretation "refl3" 'refl = (refl3 ???).

notation > "A × term 74 B ⇒ term 19 C" non associative with precedence 72 for @{'binary_morphism0 $A $B $C}.
notation > "A × term 74 B ⇒_1 term 19 C" non associative with precedence 72 for @{'binary_morphism1 $A $B $C}.
notation > "A × term 74 B ⇒_2 term 19 C" non associative with precedence 72 for @{'binary_morphism2 $A $B $C}.
notation > "A × term 74 B ⇒_3 term 19 C" non associative with precedence 72 for @{'binary_morphism3 $A $B $C}.
notation > "B ⇒_1 C" right associative with precedence 72 for @{'arrows1_SET $B $C}.
notation > "B ⇒_1. C" right associative with precedence 72 for @{'arrows1_SETlow $B $C}.
notation > "B ⇒_2 C" right associative with precedence 72 for @{'arrows2_SET1 $B $C}.
notation > "B ⇒_2. C" right associative with precedence 72 for @{'arrows2_SET1low $B $C}.

notation "A × term 74 B ⇒\sub 1 term 19 C" non associative with precedence 72 for @{'binary_morphism1 $A $B $C}.
notation "A × term 74 B ⇒\sub 2 term 19 C" non associative with precedence 72 for @{'binary_morphism2 $A $B $C}.
notation "A × term 74 B ⇒\sub 3 term 19 C" non associative with precedence 72 for @{'binary_morphism3 $A $B $C}.
notation "B ⇒\sub 1 C" right associative with precedence 72 for @{'arrows1_SET $B $C}.
notation "B ⇒\sub 2 C" right associative with precedence 72 for @{'arrows2_SET1 $B $C}.
notation "B ⇒\sub 1. C" right associative with precedence 72 for @{'arrows1_SETlow $B $C}.
notation "B ⇒\sub 2. C" right associative with precedence 72 for @{'arrows2_SET1low $B $C}.

interpretation "'binary_morphism0" 'binary_morphism0 A B C = (binary_morphism A B C).
interpretation "'arrows2_SET1 low" 'arrows2_SET1 A B = (unary_morphism2 A B).
interpretation "'arrows2_SET1low" 'arrows2_SET1low A B = (unary_morphism2 A B).
interpretation "'binary_morphism1" 'binary_morphism1 A B C = (binary_morphism1 A B C).
interpretation "'binary_morphism2" 'binary_morphism2 A B C = (binary_morphism2 A B C).
interpretation "'binary_morphism3" 'binary_morphism3 A B C = (binary_morphism3 A B C).
interpretation "'arrows1_SET low" 'arrows1_SET A B = (unary_morphism1 A B).
interpretation "'arrows1_SETlow" 'arrows1_SETlow A B = (unary_morphism1 A B).


definition unary_morphism2_of_unary_morphism1: 
  ∀S,T:setoid1.unary_morphism1 S T → unary_morphism2 (setoid2_of_setoid1 S) T.
 #S #T #u
 @mk_unary_morphism2
  [ @(fun11 ?? u)
  | @(prop11 ?? u) ]
qed.

definition CPROP: setoid1.
 @mk_setoid1
  [ @CProp[0]
  | @mk_equivalence_relation1
     [ @Iff
     | #x @mk_Iff #x1 assumption
     | #x #y #i cases i #f #f1 @mk_Iff assumption
     | #x #y #z #i1 #i cases i cases i1 #f #f1 #f2 #f3 @mk_Iff #x1
       [ @(f2 (f x1)) | @(f1 (f3 x1))]]]
qed.

definition CProp0_of_CPROP: carr1 CPROP → CProp[0] ≝ λx.x.
coercion CProp0_of_CPROP.

alias symbol "eq" = "setoid1 eq".
definition fi': ∀A,B:CPROP. A = B → B → A.
 #A #B #e #b @(fi ?? e) assumption.
qed.

notation ". r" with precedence 55 for @{'fi $r}.
interpretation "fi" 'fi r = (fi' ?? r).

definition and_morphism: binary_morphism1 CPROP CPROP CPROP.
 @mk_binary_morphism1
  [ @And
  | #a #a' #b #b' #e #e1 @mk_Iff #a1 cases a1 #a2 #b1 @Conj
     [ @(if ?? e a2)
     | @(if ?? e1 b1)
     | @(fi ?? e a2)
     | @(fi ?? e1 b1)]]
qed.

interpretation "and_morphism" 'and a b = (fun21 ??? and_morphism a b).

definition or_morphism: binary_morphism1 CPROP CPROP CPROP.
 @mk_binary_morphism1
  [ @Or
  | #a #a' #b #b' #e #e1 @mk_Iff #o cases o #a1 [1,3: @Left |2,4: @Right]
     [ @(if ?? e a1)
     | @(fi ?? e a1)
     | @(if ?? e1 a1)
     | @(fi ?? e1 a1)]]
qed.

interpretation "or_morphism" 'or a b = (fun21 ??? or_morphism a b).

definition if_morphism: binary_morphism1 CPROP CPROP CPROP.
 @mk_binary_morphism1
  [ @(λA,B. A → B)
  | #a #a' #b #b' #e #e1 @mk_Iff #f #a1
     [ @(if ?? e1) @f @(fi ?? e) assumption
     | @(fi ?? e1) @f @(if ?? e) assumption]]
qed.
(*
notation > "hvbox(a break ∘ b)" left associative with precedence 60 for @{ comp ??? $a $b }.
*)
record category : Type[1] ≝ { 
   objs:> Type[0];
   arrows: objs → objs → setoid;
   id: ∀o:objs. arrows o o;
   comp: ∀o1,o2,o3. (arrows o1 o2) × (arrows o2 o3) ⇒ (arrows o1 o3);
   comp_assoc: ∀o1,o2,o3,o4.∀a12:arrows o1 ?.∀a23:arrows o2 ?.∀a34:arrows o3 o4.
   comp o1 o3 o4 (comp o1 o2 o3 a12 a23) a34 =_0 comp o1 o2 o4 a12 (comp o2 o3 o4 a23 a34);
   id_neutral_left : ∀o1,o2. ∀a: arrows o1 o2. comp ??? (id o1) a =_0 a;
   id_neutral_right: ∀o1,o2. ∀a: arrows o1 o2. comp ??? a (id o2) =_0 a
}.
(*
notation "hvbox(a break ∘ b)" left associative with precedence 60 for @{ 'compose $a $b }.
*)
record category1 : Type[2] ≝
 { objs1:> Type[1];
   arrows1: objs1 → objs1 → setoid1;
   id1: ∀o:objs1. arrows1 o o;
   comp1: ∀o1,o2,o3. binary_morphism1 (arrows1 o1 o2) (arrows1 o2 o3) (arrows1 o1 o3);
   comp_assoc1: ∀o1,o2,o3,o4. ∀a12,a23,a34.
    comp1 o1 o3 o4 (comp1 o1 o2 o3 a12 a23) a34 =_1 comp1 o1 o2 o4 a12 (comp1 o2 o3 o4 a23 a34);
   id_neutral_right1: ∀o1,o2. ∀a: arrows1 o1 o2. comp1 ??? (id1 o1) a =_1 a;
   id_neutral_left1: ∀o1,o2. ∀a: arrows1 o1 o2. comp1 ??? a (id1 o2) =_1 a
 }.

record category2 : Type[3] ≝
 { objs2:> Type[2];
   arrows2: objs2 → objs2 → setoid2;
   id2: ∀o:objs2. arrows2 o o;
   comp2: ∀o1,o2,o3. binary_morphism2 (arrows2 o1 o2) (arrows2 o2 o3) (arrows2 o1 o3);
   comp_assoc2: ∀o1,o2,o3,o4. ∀a12,a23,a34.
    comp2 o1 o3 o4 (comp2 o1 o2 o3 a12 a23) a34 =_2 comp2 o1 o2 o4 a12 (comp2 o2 o3 o4 a23 a34);
   id_neutral_right2: ∀o1,o2. ∀a: arrows2 o1 o2. comp2 ??? (id2 o1) a =_2 a;
   id_neutral_left2: ∀o1,o2. ∀a: arrows2 o1 o2. comp2 ??? a (id2 o2) =_2 a
 }.

record category3 : Type[4] ≝
 { objs3:> Type[3];
   arrows3: objs3 → objs3 → setoid3;
   id3: ∀o:objs3. arrows3 o o;
   comp3: ∀o1,o2,o3. binary_morphism3 (arrows3 o1 o2) (arrows3 o2 o3) (arrows3 o1 o3);
   comp_assoc3: ∀o1,o2,o3,o4. ∀a12,a23,a34.
    comp3 o1 o3 o4 (comp3 o1 o2 o3 a12 a23) a34 =_3 comp3 o1 o2 o4 a12 (comp3 o2 o3 o4 a23 a34);
   id_neutral_right3: ∀o1,o2. ∀a: arrows3 o1 o2. comp3 ??? (id3 o1) a =_3 a;
   id_neutral_left3: ∀o1,o2. ∀a: arrows3 o1 o2. comp3 ??? a (id3 o2) =_3 a
 }.

notation "'ASSOC'" with precedence 90 for @{'assoc}.

interpretation "category2 composition" 'compose x y = (fun22 ??? (comp2 ????) y x).
interpretation "category2 assoc" 'assoc = (comp_assoc2 ????????).
interpretation "category1 composition" 'compose x y = (fun21 ??? (comp1 ????) y x).
interpretation "category1 assoc" 'assoc = (comp_assoc1 ????????).
interpretation "category composition" 'compose x y = (fun2 ??? (comp ????) y x).
interpretation "category assoc" 'assoc = (comp_assoc ????????).

definition category2_of_category1: category1 → category2.
 #c
 @mk_category2
  [ @(objs1 c)
  | #o #o1 @(setoid2_of_setoid1 (arrows1 c o o1))
  | @(id1 c)
  | #o1 #o2 #o3
    @mk_binary_morphism2
     [ #c1 #c2 @(comp1 c o1 o2 o3 c1 c2)
     | #a #a' #b #b' #e #e1 @(e‡e1) ]
  | #o1 #o2 #o3 #o4 #a12 #a23 #a34 @comp_assoc1
  | #o1 #o2 #a @id_neutral_right1
  | #o1 #o2 #a @id_neutral_left1 ]
qed.
(*coercion category2_of_category1.*)

record functor2 (C1: category2) (C2: category2) : Type[3] ≝
 { map_objs2:1> C1 → C2;
   map_arrows2: ∀S,T. unary_morphism2 (arrows2 ? S T) (arrows2 ? (map_objs2 S) (map_objs2 T));
   respects_id2: ∀o:C1. map_arrows2 ?? (id2 ? o) = id2 ? (map_objs2 o);
   respects_comp2:
     ∀o1,o2,o3.∀f1:arrows2 ? o1 o2.∀f2:arrows2 ? o2 o3.
     map_arrows2 ?? (f2 ∘ f1) = map_arrows2 ?? f2 ∘ map_arrows2 ?? f1}.

notation > "F⎽⇒ x" left associative with precedence 65 for @{'map_arrows2 $F $x}.
notation "F\sub⇒ x" left associative with precedence 65 for @{'map_arrows2 $F $x}.
interpretation "map_arrows2" 'map_arrows2 F x = (fun12 ?? (map_arrows2 ?? F ??) x).
(* BEGIN HERE
definition functor2_setoid: category2 → category2 → setoid3.
 #C1 #C2
 @mk_setoid3
  [ @(functor2 C1 C2)
  | @mk_equivalence_relation3
     [ #f #g
       @(∀c:C1. cic:/matita/logic/equality/eq.ind#xpointer(1/1) ? (f c) (g c));
     | simplify; intros; @cic:/matita/logic/equality/eq.ind#xpointer(1/1/1);
     | simplify; intros; @cic:/matita/logic/equality/sym_eq.con; @H;
     | simplify; intros; @cic:/matita/logic/equality/trans_eq.con;
        [2: @H; | skip | @H1;]]]
qed.

definition functor2_of_functor2_setoid: ∀S,T. functor2_setoid S T → functor2 S T ≝ λS,T,x.x.
coercion functor2_of_functor2_setoid.

definition CAT2: category3.
 constructor 1;
  [ @category2;
  | @functor2_setoid;
  | intros; constructor 1;
     [ @(λx.x);
     | intros; constructor 1;
        [ @(λx.x);
        | intros; assumption;]
     | intros; @rule #;
     | intros; @rule #; ]
  | intros; constructor 1;
     [ intros; constructor 1;
        [ intros; @(c1 (c o));
        | intros; constructor 1;
           [ intro; @(map_arrows2 ?? c1 ?? (map_arrows2 ?? c ?? c2));
           | intros; @(††e); ]
        | intros; simplify;
          @(.= †(respects_id2 : ?));
          @(respects_id2 : ?);
        | intros; simplify;
          @(.= †(respects_comp2 : ?));
          @(respects_comp2 : ?); ]
        | intros; intro; simplify;
          @(cic:/matita/logic/equality/eq_ind.con ????? (e ?));
          @(cic:/matita/logic/equality/eq_ind.con ????? (e1 ?));
          constructor 1; ]
        | intros; intro; simplify; constructor 1;
        | intros; intro; simplify; constructor 1;
        | intros; intro; simplify; constructor 1; ]
qed.

definition category2_of_objs3_CAT2: objs3 CAT2 → category2 ≝ λx.x.
coercion category2_of_objs3_CAT2.

definition functor2_setoid_of_arrows3_CAT2: ∀S,T. arrows3 CAT2 S T → functor2_setoid S T ≝ λS,T,x.x.
coercion functor2_setoid_of_arrows3_CAT2.

notation > "B ⇒_\c3 C" right associative with precedence 72 for @{'arrows3_CAT $B $C}.
notation "B ⇒\sub (\c 3) C" right associative with precedence 72 for @{'arrows3_CAT $B $C}.
interpretation "'arrows3_CAT" 'arrows3_CAT A B = (arrows3 CAT2 A B).

definition unary_morphism_setoid: setoid → setoid → setoid.
 intros;
 constructor 1;
  [ @(unary_morphism s s1);
  | constructor 1;
     [ intros (f g); @(∀a:s. eq ? (f a) (g a));
     | intros 1; simplify; intros; @refl;
     | simplify; intros; @sym; @f;
     | simplify; intros; @trans; [2: @f; | skip | @f1]]]
qed.

definition SET: category1.
 constructor 1;
  [ @setoid;
  | @rule (λS,T:setoid.setoid1_of_setoid (unary_morphism_setoid S T));
  | intros; constructor 1; [ @(λx:carr o.x); | intros; assumption ]
  | intros; constructor 1; [ intros; constructor 1; [ @(λx. c1 (c x)); | intros;
     @(† (†e));]
  | intros; whd; intros; simplify; whd in H1; whd in H;
    @trans; [ @(b (a' a1)); | l@(prop1 ?? b (a a1) (a' a1));
     [ @Hletin | @(e a1); ]  | @e1; ]]
  | intros; whd; intros; simplify; @refl;
  | intros; simplify; whd; intros; simplify; @refl;
  | intros; simplify; whd; intros; simplify; @refl;
  ]
qed.

definition setoid_of_SET: objs1 SET → setoid ≝ λx.x.
coercion setoid_of_SET.

definition unary_morphism_setoid_of_arrows1_SET: 
  ∀P,Q.arrows1 SET P Q → unary_morphism_setoid P Q  ≝ λP,Q,x.x.
coercion unary_morphism_setoid_of_arrows1_SET.

interpretation "'arrows1_SET" 'arrows1_SET A B = (arrows1 SET A B).

definition unary_morphism1_setoid1: setoid1 → setoid1 → setoid1.
 intros;
 constructor 1;
  [ @(unary_morphism1 s s1);
  | constructor 1;
     [ intros (f g);
       alias symbol "eq" = "setoid1 eq".
       @(∀a: carr1 s. f a = g a);
     | intros 1; simplify; intros; @refl1;
     | simplify; intros; @sym1; @f;
     | simplify; intros; @trans1; [2: @f; | skip | @f1]]]
qed.

definition unary_morphism1_of_unary_morphism1_setoid1 : 
  ∀S,T. unary_morphism1_setoid1 S T → unary_morphism1 S T ≝ λP,Q,x.x.
coercion unary_morphism1_of_unary_morphism1_setoid1.

definition SET1: objs3 CAT2.
 constructor 1;
  [ @setoid1;
  | @rule (λS,T.setoid2_of_setoid1 (unary_morphism1_setoid1 S T));
  | intros; constructor 1; [ @(λx.x); | intros; assumption ]
  | intros; constructor 1; [ intros; constructor 1; [ @(λx. c1 (c x)); | intros;
     @(† (†e));]
  | intros; whd; intros; simplify; whd in H1; whd in H;
    @trans1; [ @(b (a' a1)); | l@(prop11 ?? b (a a1) (a' a1));
     [ @Hletin | @(e a1); ]  | @e1; ]]
  | intros; whd; intros; simplify; @refl1;
  | intros; simplify; whd; intros; simplify; @refl1;
  | intros; simplify; whd; intros; simplify; @refl1;
  ]
qed.

interpretation "'arrows2_SET1" 'arrows2_SET1 A B = (arrows2 SET1 A B).

definition setoid1_of_SET1: objs2 SET1 → setoid1 ≝ λx.x.
coercion setoid1_of_SET1.

definition unary_morphism1_setoid1_of_arrows2_SET1: 
  ∀P,Q.arrows2 SET1 P Q → unary_morphism1_setoid1 P Q ≝ λP,Q,x.x.
coercion unary_morphism1_setoid1_of_arrows2_SET1.
 
variant objs2_of_category1: objs1 SET → objs2 SET1 ≝ setoid1_of_setoid.
coercion objs2_of_category1.

prefer coercion Type_OF_setoid. (* we prefer the lower carrier projection *)
prefer coercion Type_OF_objs1.

alias symbol "exists" (instance 1) = "CProp[2] exists".
definition full2 ≝  
  λA,B:CAT2.λF:carr3 (arrows3 CAT2 A B).
    ∀o1,o2:A.∀f.∃g:arrows2 A o1 o2.F⎽⇒ g =_2 f.
alias symbol "exists" (instance 1) = "CProp exists".
    
definition faithful2 ≝  
  λA,B:CAT2.λF:carr3 (arrows3 CAT2 A B).
    ∀o1,o2:A.∀f,g:arrows2 A o1 o2.F⎽⇒ f =_2 F⎽⇒ g → f =_2 g.
    

notation "r \sup *" non associative with precedence 90 for @{'OR_f_star $r}.
notation > "r *" non associative with precedence 90 for @{'OR_f_star $r}.

notation "r \sup (⎻* )" non associative with precedence 90 for @{'OR_f_minus_star $r}.
notation > "r⎻*" non associative with precedence 90 for @{'OR_f_minus_star $r}.

notation "r \sup ⎻" non associative with precedence 90 for @{'OR_f_minus $r}.
notation > "r⎻" non associative with precedence 90 for @{'OR_f_minus $r}.
*)