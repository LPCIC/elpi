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

include "basics/types.ma".
include "basics/bool.ma".

(****** DeqSet: a set with a decidbale equality ******)

record DeqSet : Type[1] ≝ { 
   carr :> Type[0];
   eqb: carr → carr → bool;
   eqb_true: ∀x,y. (eqb x y = true) ↔ (x = y)
}.
    
notation "a == b" non associative with precedence 45 for @{ 'eqb $a $b }.
interpretation "eqb" 'eqb a b = (eqb ? a b).

notation "\P H" non associative with precedence 90 
  for @{(proj1 … (eqb_true ???) $H)}. 

notation "\b H" non associative with precedence 90 
  for @{(proj2 … (eqb_true ???) $H)}. 
  
notation < "𝐃" non associative with precedence 90 
 for @{'bigD}.
interpretation "DeqSet" 'bigD = (mk_DeqSet ???).
  
lemma eqb_false: ∀S:DeqSet.∀a,b:S. 
  (eqb ? a b) = false ↔ a ≠ b.
#S #a #b % #H 
  [@(not_to_not … not_eq_true_false) #H1 <H @sym_eq @(\b H1)
  |cases (true_or_false (eqb ? a b)) // #H1 @False_ind @(absurd … (\P H1) H)
  ]
qed.
 
notation "\Pf H" non associative with precedence 90 
  for @{(proj1 … (eqb_false ???) $H)}. 

notation "\bf H" non associative with precedence 90 
  for @{(proj2 … (eqb_false ???) $H)}. 
  
lemma dec_eq: ∀S:DeqSet.∀a,b:S. a = b ∨ a ≠ b.
#S #a #b cases (true_or_false (eqb ? a b)) #H
  [%1 @(\P H) | %2 @(\Pf H)]
qed.

definition beqb ≝ λb1,b2.
  match b1 with [ true ⇒ b2 | false ⇒ notb b2].

notation < "a == b" non associative with precedence 45 for @{beqb $a $b }.
lemma beqb_true: ∀b1,b2. iff (beqb b1 b2 = true) (b1 = b2).
#b1 #b2 cases b1 cases b2 normalize /2/
qed. 

definition DeqBool ≝ mk_DeqSet bool beqb beqb_true.

alias symbol "hint_decl" (instance 1) = "hint_decl_Type1".
unification hint  0 ≔ ; 
    X ≟ mk_DeqSet bool beqb beqb_true
(* ---------------------------------------- *) ⊢ 
    bool ≡ carr X.
    
unification hint  0 ≔ b1,b2:bool; 
    X ≟ mk_DeqSet bool beqb beqb_true
(* ---------------------------------------- *) ⊢ 
    beqb b1 b2 ≡ eqb X b1 b2.
    
example exhint: ∀b:bool. (b == false) = true → b = false. 
#b #H @(\P H).
qed.

(* option *)

definition eq_option ≝
  λA:DeqSet.λa1,a2:option A.
    match a1 with 
    [ None ⇒ match a2 with [None ⇒ true | _ ⇒ false]
    | Some a1' ⇒ match a2 with [None ⇒ false | Some a2' ⇒ a1'==a2']].

lemma eq_option_true: ∀A:DeqSet.∀a1,a2:option A.
  eq_option A a1 a2 = true ↔ a1 = a2.
#A *
  [* 
    [% //
    |#a1 % normalize #H destruct 
    ]
  |#a1 *  
    [normalize % #H destruct
    |#a2 normalize %
      [#Heq >(\P Heq) //
      |#H destruct @(\b ?) //
      ]
  ]
qed.

definition DeqOption ≝ λA:DeqSet.
  mk_DeqSet (option A) (eq_option A) (eq_option_true A).
  
unification hint  0 ≔ C; 
    T ≟ carr C,
    X ≟ DeqOption C
(* ---------------------------------------- *) ⊢ 
    option T ≡ carr X.

unification hint  0 ≔ T,a1,a2; 
    X ≟ DeqOption T
(* ---------------------------------------- *) ⊢ 
    eq_option T a1 a2 ≡ eqb X a1 a2.


(* pairs *)
definition eq_pairs ≝
  λA,B:DeqSet.λp1,p2:A×B.(\fst p1 == \fst p2) ∧ (\snd p1 == \snd p2).

lemma eq_pairs_true: ∀A,B:DeqSet.∀p1,p2:A×B.
  eq_pairs A B p1 p2 = true ↔ p1 = p2.
#A #B * #a1 #b1 * #a2 #b2 %
  [#H cases (andb_true …H) #eqa #eqb >(\P eqa) >(\P eqb) //
  |#H destruct normalize >(\b (refl … a2)) >(\b (refl … b2)) //
  ]
qed.

definition DeqProd ≝ λA,B:DeqSet.
  mk_DeqSet (A×B) (eq_pairs A B) (eq_pairs_true A B).
  
unification hint  0 ≔ C1,C2; 
    T1 ≟ carr C1,
    T2 ≟ carr C2,
    X ≟ DeqProd C1 C2
(* ---------------------------------------- *) ⊢ 
    T1×T2 ≡ carr X.

unification hint  0 ≔ T1,T2,p1,p2; 
    X ≟ DeqProd T1 T2
(* ---------------------------------------- *) ⊢ 
    eq_pairs T1 T2 p1 p2 ≡ eqb X p1 p2.

example hint2: ∀b1,b2. 
  〈b1,true〉==〈false,b2〉=true → 〈b1,true〉=〈false,b2〉.
#b1 #b2 #H @(\P H)
qed.

(* sum *)
definition eq_sum ≝
  λA,B:DeqSet.λp1,p2:A+B.
  match p1 with
  [ inl a1 ⇒ match p2 with
    [ inl a2 ⇒ a1 == a2 | inr b2 ⇒ false ]
  | inr b1 ⇒ match p2 with 
    [ inl a2 ⇒ false | inr b2 ⇒ b1 == b2 ]
  ].

lemma eq_sum_true: ∀A,B:DeqSet.∀p1,p2:A+B.
  eq_sum A B p1 p2 = true ↔ p1 = p2.
#A #B * 
  [#a1 * 
    [#a2 normalize % 
      [#eqa >(\P eqa) // | #H destruct @(\b ?) //]
    |#b2 normalize % #H destruct 
    ]
  |#b1 *
    [#a2 normalize % #H destruct
    |#b2 normalize %
      [#eqb >(\P eqb) // | #H destruct @(\b ?) //]
    ]
  ]
qed.

definition DeqSum ≝ λA,B:DeqSet.
  mk_DeqSet (A+B) (eq_sum A B) (eq_sum_true A B).
  
unification hint  0 ≔ C1,C2; 
    T1 ≟ carr C1,
    T2 ≟ carr C2,
    X ≟ DeqSum C1 C2
(* ---------------------------------------- *) ⊢ 
    T1+T2 ≡ carr X.

unification hint  0 ≔ T1,T2,p1,p2; 
    X ≟ DeqSum T1 T2
(* ---------------------------------------- *) ⊢ 
    eq_sum T1 T2 p1 p2 ≡ eqb X p1 p2.

(* sigma *)
definition eq_sigma ≝ 
  λA:DeqSet.λP:A→Prop.λp1,p2:Σx:A.P x.
  match p1 with 
  [mk_Sig a1 h1 ⇒ 
    match p2 with 
    [mk_Sig a2 h2 ⇒ a1==a2]].
 
(* uses proof irrelevance *)
lemma eq_sigma_true: ∀A:DeqSet.∀P.∀p1,p2:Σx.P x.
  eq_sigma A P p1 p2 = true ↔ p1 = p2.
#A #P * #a1 #Ha1 * #a2 #Ha2 %
  [normalize #eqa generalize in match Ha1; >(\P eqa) // 
  |#H >H @(\b ?) //
  ]
qed.

definition DeqSig ≝ λA:DeqSet.λP:A→Prop.
  mk_DeqSet (Σx:A.P x) (eq_sigma A P) (eq_sigma_true A P).

(*
unification hint  0 ≔ C,P; 
    T ≟ carr C,
    X ≟ DeqSig C P
(* ---------------------------------------- *) ⊢ 
    Σx:T.P x ≡ carr X.

unification hint  0 ≔ T,P,p1,p2; 
    X ≟ DeqSig T P
(* ---------------------------------------- *) ⊢ 
    eq_sigma T P p1 p2 ≡ eqb X p1 p2.
*)
