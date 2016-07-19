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

include "pts_dummy_new/types.ma".

(*
inductive TJ (p: pts): list T → T → T → Prop ≝
  | ax : ∀i,j. Ax p i j → TJ p (nil T) (Sort i) (Sort j)
  | start: ∀G.∀A.∀i.TJ p G A (Sort i) → 
      TJ p (A::G) (Rel 0) (lift A 0 1)
  | weak: ∀G.∀A,B,C.∀i.
     TJ p G A B → TJ p G C (Sort i) → 
       TJ p (C::G) (lift A 0 1) (lift B 0 1)
  | prod: ∀G.∀A,B.∀i,j,k. Re p i j k →
     TJ p G A (Sort i) → TJ p (A::G) B (Sort j) → 
       TJ p G (Prod A B) (Sort k)
  | app: ∀G.∀F,A,B,a. 
     TJ p G F (Prod A B) → TJ p G a A → 
       TJ p G (App F a) (subst B 0 a)
  | abs: ∀G.∀A,B,b.∀i. 
     TJ p (A::G) b B → TJ p G (Prod A B) (Sort i) → 
       TJ p G (Lambda A b) (Prod A B)
  | conv: ∀G.∀A,B,C.∀i. Co p B C →
     TJ p G A B → TJ p G C (Sort i) → TJ p G A C
  | dummy: ∀G.∀A,B.∀i. 
     TJ p G A B → TJ p G B (Sort i) → TJ p G (D A) B.
*)

(* the definition of liftl is tricky *)
let rec liftl (G:list T) p : list T ≝  
  match G with
    [ nil ⇒ nil T
    | cons A D ⇒ ((lift A (length ? D) p)::(liftl D p))
    ].

axiom lambda_lift : ∀A,B,C. lift A 0 1 = Lambda B C →
∃P,Q. A = Lambda P Q ∧ lift P 0 1  = B ∧ lift Q 1 1 = C.

axiom prod_lift : ∀A,B,C. lift A 0 1 = Prod B C →
∃P,Q. A = Prod P Q ∧ lift P 0 1  = B ∧ lift Q 1 1 = C.

axiom dummy_lift : ∀A,B,C. lift A 0 1 = D B C →
∃P,Q. A = D P Q ∧ lift P 0 1  = B ∧ lift Q 0 1 = C.

axiom conv_lift: ∀P,M,N,k. Co P M N → Co P (lift M k 1) (lift N k 1).

lemma weak_gen: ∀P,E,M,N. E ⊢_{P} M : N → 
∀G,D,A,i. E=D@G → G ⊢_{P} A : Sort i → 
   (liftl D 1)@(A::G) ⊢_{P}  lift M (length ? D) 1 : lift N (length ? D) 1.
#Pts #E #M #N #tjMN (elim tjMN)
  [normalize #i #j #k #G #D #A #i (cases D) 
    [normalize #isnil destruct #H @start_lemma1 //
     @(glegalk … (start … H))
    |#P #L normalize #isnil destruct
    ]
  |#G #A #i #tjA #Hind #G1 #D #A1 #j (cases D) 
    [normalize #Heq #tjA1 <(lift_rel 0 1) @(weak …tjA1)
     <Heq @(start … tjA)
    |#A2 #L normalize #Heq destruct #tjA2 
     cut (S (length ? L) = 1 + length ? L + 0) // #H >H
     >lift_lift_up <plus_n_O @(start … i) @Hind //
    ]
  |#G #P #Q #R #i #tjP #tjR #Hind1 #Hind2 #G1 #D #A #j (cases D) normalize
    [#Heq #tjA @(weak … tjA) <Heq @weak //
    |#A1 #L #Heq destruct #tjA 
     cut (S (length ? L) = 1 + length ? L + 0) // #H >H
     >lift_lift_up >lift_lift_up @(weak … i);
      [<plus_n_O @Hind1 // |@Hind2 // ]
    ]
  |#G #P #Q #i #j #k #Ax #tjP #tjQ #Hind1 #Hind2
   #G1 #D #A #l #Heq #tjA normalize @(prod … Ax);
    [/2/
    |(cut (S (length T D) = (length T D)+1)) [//] 
     #Heq1 <Heq1 @(Hind2 ? (P::D)) normalize //
    ]
  |#G #P #Q #R #S #tjP #tjS #Hind1 #Hind2
   #G1 #D #A #l #Heq #tjA normalize in Hind1 ⊢ %;
   >(lift_subst_up R S 1 0 (length ? D)) @(app … (lift Q (length ? D) 1));
    [@Hind1 // |@Hind2 //]
  |#G #P #Q #R #i #tjR #tjProd #Hind1 #Hind2
   #G1 #D #A #l #Heq #tjA normalize @(abs … i); 
    [cut (∀n. S n = n +1); [//] #H <H 
     @(Hind1 G1 (P::D) … tjA) normalize //
    | normalize in Hind2; @(Hind2 …tjA) //
    ]
  |#G #P #Q #R #i #convQR #tjP #tjQ #Hind1 #Hind2
   #G1 #D #A #l #Heq #tjA
   @(conv … (conv_lift … convQR) ? (Hind2 …)) // @Hind1 //
  |#G #P #Q #i #tjP #tjQ #Hind1 #Hind2
   #G1 #D #A #l #Heq #tjA @dummy /2/ 
  ]
qed.

lemma weak_in: ∀P,G,A,B,M,N, i.
 A::G  ⊢_{P} M : N → G ⊢_{P} B : Sort i → 
   (lift A 0 1)::B::G ⊢_{P}  lift M 1 1 : lift N 1 1.
#P #G #A #B #M #N #i #tjM #tjB 
cut (∀A.(lift A 0 1)::B::G = (liftl (A::(nil ?)) 1)@(B::G)) // #H >H 
@(weak_gen … tjM … tjB) //
qed.
