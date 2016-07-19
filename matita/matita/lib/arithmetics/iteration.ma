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

include "arithmetics/nat.ma".

(* iteration *) 

let rec iter (A:Type[0]) (g:A→A) n a on n ≝
match n with 
  [O ⇒ a
  |S m ⇒ g (iter A g m a)].
  
interpretation "iteration" 'exp g i = (iter ? g i).

lemma le_iter: ∀g,a. (∀x. x ≤ g x) → ∀i. a ≤ g^i a.
#g #a #leg #i elim i //
#n #Hind @(transitive_le … Hind) @leg 
qed.  

lemma iter_iter: ∀A.∀g:A→A.∀a,b,c. 
  g^c (g^b a) = g^(b+c) a.
#A #g #a #b #c elim c 
  [<plus_n_O normalize //
  |#m #Hind <plus_n_Sm normalize @eq_f @Hind
  ]
qed.
 
lemma monotonic_iter: ∀g,a,b,i. (monotonic ? le g) → a ≤ b →  
  g^i a ≤  g^i b.
#g #a #b #i #Hmono #leab elim i //
#m #Hind normalize @Hmono //
qed.

lemma monotonic_iter2: ∀g,a,i,j. (∀x. x ≤ g x) → i ≤ j →  
  g^i a ≤  g^j a.
#g #a #i #j #leg #leij elim leij //
#m #leim #Hind normalize @(transitive_le … Hind) @leg 
qed.