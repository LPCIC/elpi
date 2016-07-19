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

include "formal_topology/categories.ma".
include "formal_topology/notation.ma".
(*
record Fo (C1,C2:CAT2) (F:arrows3 CAT2 C1 C2) : Type[2] ≝ {
  F2: C2;
  F1: C1;
  FP: map_objs2 ?? F F1 =_\ID F2
}.

notation "ℱ\sub 1 x" non associative with precedence 65 for @{'F1 $x}.
notation > "ℱ_1" non associative with precedence 90 for @{F1 ???}.
interpretation "F1" 'F1 x = (F1 ??? x). 

notation "ℱ\sub 2 x" non associative with precedence 65 for @{'F2 $x}.
notation > "ℱ_2" non associative with precedence 90 for @{F2 ???}.
interpretation "F2" 'F2 x = (F2 ??? x). 

lemma REW : ∀C1,C2: CAT2.∀F:arrows3 CAT2 C1 C2.∀X,Y:Fo ?? F.
  arrows2 C2 (F (ℱ_1 X)) (F (ℱ_1 Y)) → 
  arrows2 C2 (ℱ_2 X) (ℱ_2 Y).           
intros 5; cases X; cases Y; clear X Y; 
cases H; cases H1; intros; assumption;
qed.           

record Fm_c (C1,C2:CAT2) (F:arrows3 CAT2 C1 C2) (X,Y:Fo ?? F) : Type[2] ≝ {
  Fm2: arrows2 C2 (F2 ??? X) (F2 ??? Y);
  Fm1: arrows2 C1 (F1 ??? X) (F1 ??? Y);
  FmP: REW ?? F X Y (map_arrows2 ?? F ?? Fm1) = Fm2
}.

notation "ℳ\sub 1 x" non associative with precedence 65 for @{'Fm1 $x}.
notation > "ℳ_1" non associative with precedence 90 for @{Fm1 ?????}.
interpretation "Fm1" 'Fm1 x = (Fm1 ????? x). 

notation "ℳ\sub 2 x" non associative with precedence 65 for @{'Fm2 $x}.
notation > "ℳ_2" non associative with precedence 90 for @{Fm2 ?????}.
interpretation "Fm2" 'Fm2 x = (Fm2 ????? x). 

definition Fm : 
 ∀C1,C2: CAT2.∀F:arrows3 CAT2 C1 C2.
   Fo ?? F → Fo ?? F → setoid2. 
intros (C1 C2 F X Y); constructor 1; [apply (Fm_c C1 C2 F X Y)]
constructor 1; [apply (λf,g.Fm2 ????? f =_2 Fm2 ????? g);]
[ intro; apply refl2;
| intros 3; apply sym2; assumption;
| intros 5; apply (trans2 ?? ??? x1 x2);]
qed.

definition F_id : 
 ∀C1,C2: CAT2.∀F:arrows3 CAT2 C1 C2.∀o.Fm ?? F o o.
intros; constructor 1; 
   [ apply (id2 C2 (F2 ??? o));
   | apply (id2 C1 (F1 ??? o));
   | cases o; cases H; simplify; apply (respects_id2 ?? F);]
qed.

definition F_comp : 
  ∀C1,C2: CAT2.∀F:arrows3 CAT2 C1 C2.∀o1,o2,o3.
    (Fm ?? F o1 o2) × (Fm ?? F o2 o3) ⇒_2 (Fm ?? F o1 o3).
intros; constructor 1;
[ intros (f g); constructor 1;
    [ apply (comp2 C2 ??? (ℳ_2 f) (ℳ_2 g));
    | apply (comp2 C1 ??? (ℳ_1 f) (ℳ_1 g));
    | apply hide; cases o1 in f; cases o2 in g; cases o3; clear o1 o2 o3;
      cases H; cases H1; cases H2; intros 2; cases c; cases c1; clear c c1;
      simplify; apply (.= (respects_comp2:?)); apply (e1‡e);]
| intros 6; change with ((ℳ_2 b ∘ ℳ_2 a) = (ℳ_2 b' ∘ ℳ_2 a'));
  change in e1 with (ℳ_2 b = ℳ_2 b');
  change in e with (ℳ_2 a = ℳ_2 a');
  apply (e‡e1);]
qed.


definition Apply : ∀C1,C2: CAT2.arrows3 CAT2 C1 C2 → CAT2.
intros (C1 C2 F);
constructor 1; 
[ apply (Fo ?? F);
| apply (Fm ?? F); 
| apply F_id; 
| apply F_comp;
| intros; apply (comp_assoc2 C2 ???? (ℳ_2 a12) (ℳ_2 a23) (ℳ_2 a34));
| intros; apply (id_neutral_right2 C2 ?? (ℳ_2 a));
| intros; apply (id_neutral_left2 C2 ?? (ℳ_2 a));]
qed.

definition faithful ≝  
   λC1,C2.λF:arrows3 CAT2 C1 C2.∀S,T.∀f,g:arrows2 C1 S T.
     map_arrows2 ?? F ?? f = map_arrows2 ?? F ?? g → f=g.

definition Ylppa : ∀C1,C2: CAT2.∀F:arrows3 CAT2 C1 C2.
  faithful ?? F →  let rC2 ≝ Apply ?? F in arrows3 CAT2 rC2 C1.
intros; constructor 1;
[ intro; apply (ℱ_1 o);
| intros; constructor 1; 
  [ intros; apply (ℳ_1 c);
  | apply hide; intros; apply f;  change in e with (ℳ_2 a = ℳ_2 a');
    lapply (FmP ????? a) as H1; lapply (FmP ????? a') as H2;
    cut (REW ????? (map_arrows2 ?? F ?? (ℳ_1 a)) = 
         REW ????? (map_arrows2 ?? F ?? (ℳ_1 a')));[2:
      apply (.= H1); apply (.= e); apply (H2^-1);]
    clear H1 H2 e; cases S in a a' Hcut; cases T;
    cases H; cases H1; simplify; intros; assumption;]
| intro; apply rule #;
| intros; simplify; apply rule #;]
qed.



*)
