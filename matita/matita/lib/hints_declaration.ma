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

(* 

Notation for hint declaration
==============================

The idea is to write a context, with abstraction first, then
recursive calls (let-in) and finally the two equivalent terms.
The context can be empty. Note the ; to begin the second part of
the context (necessary even if the first part is empty). 

 unification hint PREC \coloneq
   ID : TY, ..., ID : TY
   ; ID \equest T, ..., ID \equest T
   \vdash T1 \equiv T2       

With unidoce and some ASCII art it looks like the following:

 unification hint PREC ≔ ID : TY, ..., ID : TY;
    ID ≟ T, ..., ID ≟ T
 (*---------------------*) ⊢
         T1 ≡ T2       

The order of premises is relevant, since they are processed in order
(left to right).

*)
   
(* it seems unbelivable, but it works! *)
notation > "≔ (list0 ( (list1 (ident x) sep , ) opt (: T) ) sep ,) opt (; (list1 (ident U ≟ term 19 V ) sep ,)) ⊢ term 19 Px ≡ term 19 Py"
  with precedence 90
  for @{ ${ fold right 
               @{ ${ default 
                    @{ ${ fold right 
                        @{ 'hint_decl $Px $Py } 
                        rec acc1 @{ let ( ${ident U} : ?) ≝ $V in $acc1} } }
                    @{ 'hint_decl $Px $Py } 
                 }
               } 
               rec acc @{ 
                 ${ fold right @{ $acc } rec acc2 
                      @{ ∀${ident x}:${ default @{ $T } @{ ? } }.$acc2 } } 
               }
       }}.

(* it seems unbelivable, but it works! *)
notation > "≔ (list0 ( (list1 (ident x) sep , ) opt (: T) ) sep ,) opt (; (list1 (ident U ≟ term 19 V ) sep ,)) ⊢ term 19 Px ≡≡ term 19 Py"
  with precedence 90
  for @{ ${ fold right 
               @{ ${ default 
                    @{ ${ fold right 
                        @{ 'hint_decl2 $Px $Py } 
                        rec acc1 @{ let ( ${ident U} : ?) ≝ $V in $acc1} } }
                    @{ 'hint_decl2 $Px $Py } 
                 }
               } 
               rec acc @{ 
                 ${ fold right @{ $acc } rec acc2 
                      @{ ∀${ident x}:${ default @{ $T } @{ ? } }.$acc2 } } 
               }
       }}.

include "basics/pts.ma".

definition hint_declaration_Type0  ≝  λA:Type[0] .λa,b:A.Prop.
definition hint_declaration_Type1  ≝  λA:Type[1].λa,b:A.Prop.
definition hint_declaration_Type2  ≝  λa,b:Type[2].Prop.
definition hint_declaration_CProp0 ≝  λA:CProp[0].λa,b:A.Prop.
definition hint_declaration_CProp1 ≝  λA:CProp[1].λa,b:A.Prop.
definition hint_declaration_CProp2 ≝  λa,b:CProp[2].Prop.
  
interpretation "hint_decl_Type2"  'hint_decl2 a b = (hint_declaration_Type2 a b).
interpretation "hint_decl_CProp2" 'hint_decl2 a b = (hint_declaration_CProp2 a b).
interpretation "hint_decl_Type1"  'hint_decl a b = (hint_declaration_Type1 ? a b).
interpretation "hint_decl_CProp1" 'hint_decl a b = (hint_declaration_CProp1 ? a b).
interpretation "hint_decl_CProp0" 'hint_decl a b = (hint_declaration_CProp0 ? a b).
interpretation "hint_decl_Type0"  'hint_decl a b = (hint_declaration_Type0 ? a b).

(* Non uniform coercions support
record solution2 (S : Type[2]) (s : S) : Type[3] ≝ {
  target2 : Type[2];
  result2  : target2
}.

record solution1 (S : Type[1]) (s : S) : Type[2] ≝ {
  target1 : Type[1];
  result1  : target1
}.

coercion nonunifcoerc1 : ∀S:Type[1].∀s:S.∀l:solution1 S s. target1 S s l ≝ result1 
 on s : ? to target1 ???.

coercion nonunifcoerc2 : ∀S:Type[2].∀s:S.∀l:solution2 S s. target2 S s l ≝ result2
 on s : ? to target2 ???.
*)

(* Example of a non uniform coercion declaration 
   
     Type[0]              setoid
                >--->     
     MR                   R  

   provided MR = carr R

unification hint 0 ≔ R : setoid;
   MR ≟ carr R, 
   sol ≟ mk_solution1 Type[0] MR setoid R 
(* ---------------------------------------- *) ⊢ 
   setoid ≡ target1 ? MR sol.

*)
