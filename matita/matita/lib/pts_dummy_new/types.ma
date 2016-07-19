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

include "pts_dummy_new/subst.ma".
include "basics/lists/list.ma".


(*************************** substl *****************************)

let rec substl (G:list T) (N:T) : list T ≝  
  match G with
    [ nil ⇒ nil T
    | cons A D ⇒ ((subst A (length T D) N)::(substl D N))
    ].

(*
nlemma substl_cons: ∀A,N.∀G.
substl (A::G) N = (subst_aux A (length T G) N)::(substl G N).
//; nqed.
*)

(*start: ∀G.∀A.∀i.TJ G A (Sort i) → TJ (A::G) (Rel 0) (lift A 0 1)
  | 
nlemma length_cons: ∀A.∀G. length T (A::G) = length T G + 1.
/2/; nqed.*)

(****************************************************************)

(*
axiom A: nat → nat → Prop.
axiom R: nat → nat → nat → Prop.
axiom conv: T → T → Prop.*)

record pts : Type[0] ≝ {
  Ax: nat → nat → Prop;
  Re: nat → nat → nat → Prop;
  Co: T → T → Prop
  }.
  
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
     TJ p G A B → TJ p G B (Sort i) → TJ p G (D A B) B.
     
interpretation "generic type judgement" 'TJT P G A B = (TJ P G A B).

notation "hvbox( G break  ⊢ _{P} A break : B)"
   non associative with precedence 45
   for @{'TJT $P $G $A $B}.
   
(* ninverter TJ_inv2 for TJ (%?%) : Prop. *)

(**** definitions ****)

inductive Glegal (P:pts) (G: list T) : Prop ≝
glegalk : ∀A,B. G ⊢_{P} A : B → Glegal P G.

inductive Gterm (P:pts) (G: list T) (A:T) : Prop ≝
  | is_term: ∀B.G ⊢_{P} A:B → Gterm P G A
  | is_type: ∀B.G ⊢_{P} B:A → Gterm P G A.

inductive Gtype (P:pts) (G: list T) (A:T) : Prop ≝ 
gtypek: ∀i.G ⊢_{P} A : Sort i → Gtype P G A.

inductive Gelement (P:pts) (G:list T) (A:T) : Prop ≝
gelementk: ∀B.G ⊢_{P} A:B → Gtype P G B → Gelement P G A.

inductive Tlegal (P:pts) (A:T) : Prop ≝ 
tlegalk: ∀G. Gterm P G A → Tlegal P A.

(*
ndefinition Glegal ≝ λG: list T.∃A,B:T.TJ G A B .

ndefinition Gterm ≝ λG: list T.λA.∃B.TJ G A B ∨ TJ G B A.

ndefinition Gtype ≝ λG: list T.λA.∃i.TJ G A (Sort i).

ndefinition Gelement ≝ λG: list T.λA.∃B.TJ G A B ∨ Gtype G B.

ndefinition Tlegal ≝ λA:T.∃G: list T.Gterm G A.
*)

(*
ntheorem free_var1: ∀G.∀A,B,C. TJ G A B →
subst C A 
#G; #i; #j; #axij; #Gleg; ncases Gleg; 
#A; #B; #tjAB; nelim tjAB; /2/; (* bello *) nqed.
*)

theorem start_lemma1: ∀P,G,i,j. 
Ax P i j → Glegal P G → G ⊢_{P} Sort i: Sort j.
#P #G #i #j #axij #Gleg (cases Gleg) 
#A #B #tjAB (elim tjAB) /2/
(* bello *) qed.

theorem start_rel: ∀P,G,A,C,n,i,q.
G ⊢_{P} C: Sort q → G ⊢_{P} Rel n: lift A 0 i → 
 C::G ⊢_{P} Rel (S n): lift A 0 (S i).
#P #G #A #C #n #i #p #tjC #tjn
 (applyS (weak P G (Rel n))) //. 
qed.
  
theorem start_lemma2: ∀P,G.
Glegal P G → ∀n. n < |G| → G ⊢_{P} Rel n: lift (nth n T G (Rel O)) 0 (S n).
#P #G #Gleg (cases Gleg) #A #B #tjAB (elim tjAB) /2/
  [#i #j #axij #p normalize #abs @(False_ind) @(absurd … abs) // 
  |#G #A #i #tjA #Hind #m (cases m) /2/
   #p #Hle @start_rel // @Hind @le_S_S_to_le @Hle
  |#G #A #B #C #i #tjAB #tjC #Hind1 #_ #m (cases m)
     /2/ #p #Hle @start_rel // @Hind1 @le_S_S_to_le @Hle
  ]
qed. 

axiom conv_subst: ∀T,P,Q,N,i.Co T P Q → Co T P[i := N] Q[i := N].

theorem substitution_tj: 
∀P,E.∀A,B,M. E ⊢_{P} M:B → ∀G,D.∀N. E = D@A::G → G ⊢_{P} N:A → 
  ((substl D N)@G) ⊢_{P} M[|D| := N]: B[|D| := N].
#Pts #E #A #B #M #tjMB (elim tjMB)
  [normalize #i #j #k #G #D #N (cases D) 
    [normalize #isnil destruct
    |#P #L normalize #isnil destruct
    ]
  |#G #A1 #i #tjA #Hind #G1 #D (cases D) 
    [#N #Heq #tjN >(delift (lift N O O) A1 O O O ??) //
     normalize in Heq; destruct normalize /2/
    |#H #L #N1 #Heq normalize in Heq;
     #tjN1 normalize destruct; (applyS start) /2/
    ]
  |#G #P #Q #R #i #tjP #tjR #Hind1 #Hind2 #G1 #D #N
   (cases D) normalize
    [#Heq destruct #tjN //
    |#H #L #Heq #tjN1 destruct;
       (* napplyS weak non va *)
     (cut (S (length T L) = (length T L)+0+1)) [//] 
     #Hee (applyS weak) /2/
    ]
  |#G #P #Q #i #j #k #Ax #tjP #tjQ #Hind1 #Hind2
   #G1 #D #N #Heq #tjN normalize @(prod … Ax);
    [/2/
    |(cut (S (length T D) = (length T D)+1)) [//] 
     #Heq1 <Heq1 @(Hind2 ? (P::D)) normalize //
    ]
  |#G #P #Q #R #S #tjP #tjS #Hind1 #Hind2
   #G1 #D #N #Heq #tjN normalize in Hind1 ⊢ %;
   >(plus_n_O (length ? D)) in ⊢ (? ? ? ? (? ? % ?));
   >(subst_lemma R S N ? 0) applyS app /2/
  |#G #P #Q #R #i #tjR #tjProd #Hind1 #Hind2
   #G1 #D #N #Heq #tjN normalize
   (applyS abs) 
    [normalize in Hind2; /2/
    |(* napplyS (Hind1 G1 (P::D) N ? tjN); sistemare *)
     generalize in match (Hind1 G1 (P::D) N ? tjN);
      [#H normalize in H; applyS H | normalize // ]
    ]
  |#G #P #Q #R #i #convQR #tjP #tjQ #Hind1 #Hind2
   #G1 #D #N #Heq #tjN
   @(conv …(conv_subst … convQR) ? (Hind2 …)) // @Hind1 //
  |#G #P #Q #i #tjP #tjQ #Hind1 #Hind2
   #G1 #D #N #Heq #tjN @dummy /2/ 
  ]
qed.

lemma tj_subst_0: ∀P,G,v,w. G ⊢_{P} v : w → ∀t,u. w :: G ⊢_{P} t : u →
                  G ⊢_{P} t[0≝v] : u[0≝v].
#P #G #v #w #Hv #t #u #Ht 
lapply (substitution_tj … Ht ? ([]) … Hv) normalize //
qed.
