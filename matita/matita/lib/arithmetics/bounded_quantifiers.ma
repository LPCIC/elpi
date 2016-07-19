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

include "arithmetics/nat.ma".

lemma decidable_not: ∀P. decidable P → decidable (¬P).
#P * #H [%2 % * /2/ | /2/] 
qed.

lemma decidable_or: ∀P,Q. decidable P → decidable Q → decidable (P∨Q).
#P #Q * #HP [#_ %1 %1 // |* #HQ [ %1 %2 // | %2 % * /2/] 
qed.

lemma decidable_forall: ∀P. (∀i.decidable (P i))→ 
  ∀n.decidable (∀i. i < n → P i).
#P #Hdec #n elim n
  [%1 #i #lti0 @False_ind @(absurd … lti0) @le_to_not_lt //
  |#m * #H
    [cases (Hdec m) #HPm
      [%1 #i #lei0 cases (le_to_or_lt_eq … lei0) #H1
        [@H @le_S_S_to_le @H1 |>(injective_S … H1) @HPm]
      |%2 @(not_to_not … HPm) #H1 @H1 //
      ]
    |%2 @(not_to_not … H) #H1 #i #leim @H1 @le_S //
    ]
  ]
qed.

lemma not_exists_to_forall: ∀P,n.
  ¬(∃i. i < n ∧ P i) → ∀i. i < n → ¬ P i.
#P #n elim n 
  [#_ #i #lti0 @False_ind @(absurd … lti0) @le_to_not_lt //
  |#m #Hind #H1 #i #leiS cases (le_to_or_lt_eq … leiS) #H2
    [@(Hind … (le_S_S_to_le … H2)) @(not_to_not … H1) *
     #a * #leam #Pa %{a} % // @le_S //
    |@(not_to_not … H1) #Pi %{i} % //
    ]
  ]
qed. 
 
lemma not_forall_to_exists: ∀P,n. (∀i.decidable (P i)) → 
  ¬(∀i. i < n → P i) → (∃i. i < n ∧ ¬ (P i)).
#P #n #decP elim n
  [* #H @False_ind @H #i #lti0 @False_ind @(absurd … lti0) @le_to_not_lt //
  |#m #Hind #H1 cases (decP m) #H2
    [cases (Hind ?)
      [#i * #leim #nPi %{i} % // @le_S //
      |@(not_to_not … H1) #H3 #i #leiS cases (le_to_or_lt_eq … leiS)
        [#ltiS @H3 @le_S_S_to_le // |#eqi //]
      ]
    |%{m} % //
    ]
  ]
qed.