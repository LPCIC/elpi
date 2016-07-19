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

include "arithmetics/bounded_quantifiers.ma".
include "basics/lists/list.ma".

(* A bit of combinatorics *)
interpretation "list membership" 'mem a l = (mem ? a l).

lemma decidable_mem_nat: ∀n:nat.∀l. decidable (n ∈ l).
#n #l elim l
  [%2 % @False_ind |#a #tl #Htl @decidable_or //]
qed.

lemma length_unique_le: ∀n,l. unique ? l  → (∀x. x ∈ l → x < n) → |l| ≤ n.
#n elim n 
  [* // #a #tl #_ #H @False_ind @(absurd (a < 0)) 
    [@H %1 % | @le_to_not_lt //]
  |#m #Hind #l #Huni #Hmem <(filter_length2 ? (eqb m) l)
   lapply (length_filter_eqb … m l Huni) #Hle
   @(transitive_le ? (1+|filter ? (λx.¬ eqb m x) l|))
    [@le_plus // 
    |@le_S_S @Hind
      [@unique_filter // 
      |#x #memx cut (x ≤ m)
        [@le_S_S_to_le @Hmem @(mem_filter … memx)] #Hcut
       cases(le_to_or_lt_eq … Hcut) // #eqxm @False_ind
       @(absurd ? eqxm) @sym_not_eq @eqb_false_to_not_eq
       @injective_notb @(mem_filter_true ???? memx)
      ]
    ]
  ]
qed.    

lemma eq_length_to_mem : ∀n,l. |l| = S n → unique ? l → 
  (∀x. x ∈ l → x ≤ n) → n ∈ l.
#n #l #H1 #H2 #H3 cases (decidable_mem_nat n l) // 
#H4 @False_ind @(absurd (|l| > n))
  [>H1 // 
  |@le_to_not_lt @length_unique_le //
   #x #memx cases(le_to_or_lt_eq … (H3 x memx)) //
   #Heq @not_le_to_lt @(not_to_not … H4) #_ <Heq //
  ]
qed.

lemma eq_length_to_mem_all: ∀n,l. |l| = n → unique ? l  → 
  (∀x. x ∈ l → x < n) → ∀i. i < n → i ∈ l.
#n elim n
  [#l #_ #_ #_ #i #lti0 @False_ind @(absurd ? lti0 (not_le_Sn_O ?))
  |#m #Hind #l #H #H1 #H2 #i #lei cases (le_to_or_lt_eq … lei)
    [#leim @(mem_filter… (λi.¬(eqb m i))) 
     cases (filter_eqb m … H1)
      [2: * #H @False_ind @(absurd ?? H) @eq_length_to_mem //
       #x #memx @le_S_S_to_le @H2 //]
      * #memm #Hfilter @Hind
        [@injective_S <H <(filter_length2 ? (eqb m) l) >Hfilter %
        |@unique_filter @H1
        |#x #memx cases (le_to_or_lt_eq … (H2 x (mem_filter … memx))) #H3
          [@le_S_S_to_le @H3
          |@False_ind @(absurd (m=x)) [@injective_S //] @eqb_false_to_not_eq
           @injective_notb >(mem_filter_true ???? memx) %
          ]
      |@le_S_S_to_le @leim
      ]
    |#eqi @eq_length_to_mem >eqi [@H |@H1 |#x #Hx @le_S_S_to_le >eqi @H2 //]
    ]
  ]
qed. 

lemma lt_length_to_not_mem: ∀n,l. unique ? l  → (∀x. x ∈ l → x < n) → |l| < n →
∃i. i < n ∧ ¬ (i ∈ l). 
#n elim n
  [#l #_ #_ #H @False_ind /2/
  |#m #Hind #l #Huni #Hmem #Hlen cases (filter_eqb m … Huni)
    [2: * #H #_ %{m} % //
    |* #memm #Hfilter cases (Hind (filter ? (λx. ¬(eqb m x)) l) ? ? ?)
      [#i * #ltim #memi %{i} % [@le_S // ]
       @(not_to_not … memi) @mem_filter_l @injective_notb >notb_notb
       @not_eq_to_eqb_false @sym_not_eq @lt_to_not_eq //
      |@unique_filter //
      |#x #memx cases (le_to_or_lt_eq … (Hmem x ?))
        [#H @le_S_S_to_le @H
        |#H @False_ind @(absurd (m=x)) [@injective_S //] @eqb_false_to_not_eq
         @injective_notb >(mem_filter_true ???? memx) %
        |@(mem_filter … memx)
        ]
      |<(filter_length2 … (eqb m)) in Hlen; >Hfilter #H
       @le_S_S_to_le @H
      ]
    ]
  ]
qed.