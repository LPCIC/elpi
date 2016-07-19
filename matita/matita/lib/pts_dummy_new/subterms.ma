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

inductive subterm : T → T → Prop ≝
  | appl : ∀M,N. subterm M (App M N)
  | appr : ∀M,N. subterm N (App M N)
  | lambdal : ∀M,N. subterm M (Lambda M N)
  | lambdar : ∀M,N. subterm N (Lambda M N)
  | prodl : ∀M,N. subterm M (Prod M N)
  | prodr : ∀M,N. subterm N (Prod M N)
  | dl : ∀M,N. subterm M (D M N)
  | dr : ∀M,N. subterm N (D M N)
  | sub_trans : ∀M,N,P. subterm M N → subterm N P → subterm M P.

inverter subterm_myinv for subterm (?%).

lemma subapp: ∀S,M,N. subterm S (App M N) →
 S = M ∨ S = N ∨ subterm S M ∨ subterm S N. 
#S #M #N #subH (@(subterm_myinv … subH))
  [#M1 #N1 #eqapp destruct /4/
  |#M1 #N1 #eqapp destruct /4/
  |3,4,5,6,7,8: #M1 #N1 #eqapp destruct
  |#M1 #N1 #P #sub1 #sub2 #H1 #H2 #eqapp
   (cases (H2 eqapp))
    [* [* /3/ | #subN1 %1 %2 /2/ ] 
    |#subN1 %2 /2/
    ]
  ]
qed.
 
lemma sublam: ∀S,M,N. subterm S (Lambda M N) →
 S = M ∨ S = N ∨ subterm S M ∨ subterm S N. 
#S #M #N #subH (@(subterm_myinv … subH))
  [1,2,5,6,7,8: #M1 #N1 #eqH destruct
  |3,4:#M1 #N1 #eqH destruct /4/
  |#M1 #N1 #P #sub1 #sub2 #H1 #H2 #eqH
   (cases (H2 eqH))
    [* [* /3/ | #subN1 %1 %2 /2/ ] 
    |#subN1 %2 /2/
    ]
  ]
qed.  

lemma subprod: ∀S,M,N. subterm S (Prod M N) →
 S = M ∨ S = N ∨ subterm S M ∨ subterm S N. 
#S #M #N #subH (@(subterm_myinv … subH))
  [1,2,3,4,7,8: #M1 #N1 #eqH destruct
  |5,6:#M1 #N1 #eqH destruct /4/
  |#M1 #N1 #P #sub1 #sub2 #H1 #H2 #eqH
   (cases (H2 eqH))
    [* [* /3/ | #subN1 %1 %2 /2/ ] 
    |#subN1 %2 /2/
    ]
  ]
qed.

lemma subd: ∀S,M,N. subterm S (D M N) →
 S = M ∨ S = N ∨ subterm S M ∨ subterm S N. 
#S #M #N #subH (@(subterm_myinv … subH))
  [1,2,3,4,5,6: #M1 #N1 #eqH destruct
  |7,8: #M1 #N1 #eqH destruct /4/
  |#M1 #N1 #P #sub1 #sub2 #_ #H #eqH
    (cases (H eqH))
    [* [* /3/ | #subN1 %1 %2 /2/ ] 
    |#subN1 %2 /2/
    ]
  ]
qed.    

lemma subsort: ∀S,n. ¬ subterm S (Sort n).
#S #n % #subH (@(subterm_myinv … subH))
  [1,2,3,4,5,6,7,8: #M1 #N1 #eqH destruct
  |/2/
  ]
qed.

lemma subrel: ∀S,n. ¬ subterm S (Rel n).
#S #n % #subH (@(subterm_myinv … subH))
  [1,2,3,4,5,6,7,8: #M1 #N1 #eqH destruct
  |/2/
  ]
qed.

theorem Telim: ∀P: T → Prop. (∀M. (∀N. subterm N M → P N) → P M) →
 ∀M. P M.
#P #H #M (cut (P M ∧ (∀N. subterm N M → P N)))
  [2: * //]
(elim M)
  [#n %
    [@H #N1 #subN1 @False_ind /2/
    |#N #subN1 @False_ind /2/
    ]
  |#n %
    [@H #N1 #subN1 @False_ind /2/
    |#N #subN1 @False_ind /2/
    ]
  |#M1 #M2 * #PM1 #Hind1 * #PM2 #Hind2 
   (cut (∀N.subterm N (App M1 M2) → P N))
    [#N1 #subN1 (cases (subapp … subN1))
      [* [* // | @Hind1 ] | @Hind2 ]]
    #Hcut % /3/
  |#M1 #M2 * #PM1 #Hind1 * #PM2 #Hind2 
   (cut (∀N.subterm N (Lambda M1 M2) → P N))
    [#N1 #subN1 (cases (sublam … subN1))
      [* [* // | @Hind1 ] | @Hind2 ]]
   #Hcut % /3/
  |#M1 #M2 * #PM1 #Hind1 * #PM2 #Hind2 
   (cut (∀N.subterm N (Prod M1 M2) → P N))
    [#N1 #subN1 (cases (subprod … subN1))
      [* [* // | @Hind1 ] | @Hind2 ]]
   #Hcut % /3/   
  |#M1 #M2 * #PM1 #Hind1 * #PM2 #Hind2 
   (cut (∀N.subterm N (D M1 M2) → P N))
    [#N1 #subN1 (cases (subd … subN1))
      [* [* // | @Hind1 ] | @Hind2 ]]
   #Hcut % /3/  
  ]  
qed.

let rec size M ≝
match M with
  [Sort N ⇒ 1
  |Rel N ⇒ 1
  |App P Q ⇒ size P + size Q + 1
  |Lambda P Q ⇒ size P + size Q + 1
  |Prod P Q ⇒ size P + size Q + 1
  |D P Q ⇒ size P + size Q + 1
  ]
.

(* axiom pos_size: ∀M. 1 ≤ size M. *)

theorem Telim_size: ∀P: T → Prop. 
 (∀M. (∀N. size N < size M → P N) → P M) → ∀M. P M.
#P #H #M (cut (∀p,N. size N = p → P N))
  [2: /2/]
#p @(nat_elim1 p) #m #H1 #N #sizeN @H #N0 #Hlt @(H1 (size N0)) //
qed.

(* size of subterms *)

lemma size_subterm : ∀N,M. subterm N M → size N < size M.
#N #M #subH (elim subH) normalize //
#M1 #N1 #P #sub1 #sub2 #size1 #size2 @(transitive_lt … size1 size2)
qed.
