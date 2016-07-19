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

include "formal_topology/basic_pairs.ma".
include "formal_topology/o-basic_pairs.ma".
include "formal_topology/relations_to_o-algebra.ma".
(*
definition o_basic_pair_of_basic_pair: basic_pair → Obasic_pair.
 intro b;
 constructor 1;
  [ apply (POW (concr b));
  | apply (POW (form b));
  | apply (POW⎽⇒ ?); apply (rel b); ]
qed.

definition o_relation_pair_of_relation_pair:
 ∀BP1,BP2. relation_pair BP1 BP2 →
  Orelation_pair (o_basic_pair_of_basic_pair BP1) (o_basic_pair_of_basic_pair BP2).
 intros;
 constructor 1;
  [ unfold o_basic_pair_of_basic_pair; simplify; apply (POW⎽⇒ ?); apply (r\sub \c); 
  | apply (map_arrows2 ?? POW (form BP1) (form BP2) (r \sub \f));
  | apply (.= (respects_comp2 ?? POW (concr BP1) (concr BP2) (form BP2)  r\sub\c (⊩\sub BP2) )^-1);
    cut ( ⊩ \sub BP2 ∘ r \sub \c =_12 r\sub\f ∘ ⊩ \sub BP1) as H;
    [ apply (.= †H);
      apply (respects_comp2 ?? POW (concr BP1) (form BP1) (form BP2) (⊩\sub BP1) r\sub\f);
    | apply commute;]]
qed.

lemma o_relation_pair_of_relation_pair_is_morphism : 
  ∀S,T:category2_of_category1 BP.    
  ∀a,b:arrows2 (category2_of_category1 BP) S T.a=b → 
   (eq2 (arrows2 OBP (o_basic_pair_of_basic_pair S) (o_basic_pair_of_basic_pair T))) 
    (o_relation_pair_of_relation_pair S T a) (o_relation_pair_of_relation_pair S T b).
intros 2 (S T);       
      intros (a b Eab); split; unfold o_relation_pair_of_relation_pair; simplify;
       unfold o_basic_pair_of_basic_pair; simplify;
       [ change in match or_f_minus_star_ with (λq,w,x.fun12 ?? (or_f_minus_star q w) x); 
       | change in match or_f_minus_ with (λq,w,x.fun12 ?? (or_f_minus q w) x);
       | change in match or_f_ with (λq,w,x.fun12 ?? (or_f q w) x);
       | change in match or_f_star_ with (λq,w,x.fun12 ?? (or_f_star q w) x);]
       simplify;
       apply (prop12);
       apply (.= (respects_comp2 ?? POW (concr S) (concr T) (form T) (a\sub\c) (⊩\sub T))^-1);
       apply sym2;
       apply (.= (respects_comp2 ?? POW (concr S) (concr T) (form T) (b\sub\c) (⊩\sub T))^-1);
       apply sym2;
       apply prop12;
       apply Eab;
qed.

lemma o_relation_pair_of_relation_pair_morphism : 
  ∀S,T:category2_of_category1 BP.
  unary_morphism2 (arrows2 (category2_of_category1 BP) S T)
   (arrows2 OBP (o_basic_pair_of_basic_pair S) (o_basic_pair_of_basic_pair T)).
intros (S T);
   constructor 1;
     [ apply (o_relation_pair_of_relation_pair S T);
     | apply (o_relation_pair_of_relation_pair_is_morphism S T)]
qed.

lemma o_relation_pair_of_relation_pair_morphism_respects_id:
 ∀o:category2_of_category1 BP.
  o_relation_pair_of_relation_pair_morphism o o (id2 (category2_of_category1 BP) o)
  = id2 OBP (o_basic_pair_of_basic_pair o).
   simplify; intros; whd; split; 
       [ change in match or_f_minus_star_ with (λq,w,x.fun12 ?? (or_f_minus_star q w) x); 
       | change in match or_f_minus_ with (λq,w,x.fun12 ?? (or_f_minus q w) x);
       | change in match or_f_ with (λq,w,x.fun12 ?? (or_f q w) x);
       | change in match or_f_star_ with (λq,w,x.fun12 ?? (or_f_star q w) x);]
    simplify;
    apply prop12;
    apply prop22;[2,4,6,8: apply rule #;]
    apply (respects_id2 ?? POW (concr o));
qed. 

lemma o_relation_pair_of_relation_pair_morphism_respects_comp:
  ∀o1,o2,o3:category2_of_category1 BP.
  ∀f1:arrows2 (category2_of_category1 BP) o1 o2.
  ∀f2:arrows2 (category2_of_category1 BP) o2 o3.
  (eq2 (arrows2 OBP (o_basic_pair_of_basic_pair o1) (o_basic_pair_of_basic_pair o3)))
    (o_relation_pair_of_relation_pair_morphism o1 o3 (f2 ∘ f1))
    (comp2 OBP ???
      (o_relation_pair_of_relation_pair_morphism o1 o2 f1)
      (o_relation_pair_of_relation_pair_morphism o2 o3 f2)).
   simplify; intros; whd; split;
       [ change in match or_f_minus_star_ with (λq,w,x.fun12 ?? (or_f_minus_star q w) x); 
       | change in match or_f_minus_ with (λq,w,x.fun12 ?? (or_f_minus q w) x);
       | change in match or_f_ with (λq,w,x.fun12 ?? (or_f q w) x);
       | change in match or_f_star_ with (λq,w,x.fun12 ?? (or_f_star q w) x);]
    simplify;
    apply prop12;
    apply prop22;[2,4,6,8: apply rule #;]
    apply (respects_comp2 ?? POW (concr o1) (concr o2) (concr o3) f1\sub\c f2\sub\c);
qed.

definition BP_to_OBP: carr3 (arrows3 CAT2 (category2_of_category1 BP) OBP).
 constructor 1;
  [ apply o_basic_pair_of_basic_pair;
  | intros; apply o_relation_pair_of_relation_pair_morphism;
  | apply o_relation_pair_of_relation_pair_morphism_respects_id;
  | apply o_relation_pair_of_relation_pair_morphism_respects_comp;]
qed.

theorem BP_to_OBP_faithful: faithful2 ?? BP_to_OBP.
 intros 5 (S T); change with ( (⊩) ∘ f \sub \c = (⊩) ∘ g \sub \c);
 apply (POW_faithful);
 apply (.= respects_comp2 ?? POW (concr S) (concr T) (form T) f \sub \c (⊩ \sub T));
 apply sym2;
 apply (.= respects_comp2 ?? POW (concr S) (concr T) (form T) g \sub \c (⊩ \sub T));
 apply sym2;
 apply e;
qed.

theorem BP_to_OBP_full: full2 ?? BP_to_OBP. 
 intros 3 (S T); 
 cases (POW_full (concr S) (concr T) (Oconcr_rel ?? f)) (gc Hgc);
 cases (POW_full (form S) (form T) (Oform_rel ?? f)) (gf Hgf);
 exists[
   constructor 1; [apply gc|apply gf]
   apply (POW_faithful);
   apply (let xxxx ≝POW in .= respects_comp2 ?? POW (concr S) (concr T) (form T) gc (rel T));
   apply rule (.= Hgc‡#);
   apply (.= Ocommute ?? f);
   apply (.= #‡Hgf^-1);
   apply (let xxxx ≝POW in (respects_comp2 ?? POW (concr S) (form S) (form T) (rel S) gf)^-1)]
 split;
  [ change in match or_f_minus_star_ with (λq,w,x.fun12 ?? (or_f_minus_star q w) x); 
  | change in match or_f_minus_ with (λq,w,x.fun12 ?? (or_f_minus q w) x);
  | change in match or_f_ with (λq,w,x.fun12 ?? (or_f q w) x);
  | change in match or_f_star_ with (λq,w,x.fun12 ?? (or_f_star q w) x);]
 simplify; apply (†(Hgc‡#));
qed.   
*)
