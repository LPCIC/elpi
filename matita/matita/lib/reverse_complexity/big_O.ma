
include "arithmetics/nat.ma".
include "basics/sets.ma".

(******************************** big O notation ******************************)

(*  O f g means g ∈ O(f) *)
definition O: relation (nat→nat) ≝
  λf,g. ∃c.∃n0.∀n. n0 ≤ n → g n ≤ c* (f n).
  
lemma O_refl: ∀s. O s s.
#s %{1} %{0} #n #_ >commutative_times <times_n_1 @le_n qed.

lemma O_trans: ∀s1,s2,s3. O s2 s1 → O s3 s2 → O s3 s1. 
#s1 #s2 #s3 * #c1 * #n1 #H1 * #c2 * # n2 #H2 %{(c1*c2)}
%{(max n1 n2)} #n #Hmax 
@(transitive_le … (H1 ??)) [@(le_maxl … Hmax)]
>associative_times @le_times [//|@H2 @(le_maxr … Hmax)]
qed.

lemma sub_O_to_O: ∀s1,s2. O s1 ⊆ O s2 → O s2 s1.
#s1 #s2 #H @H // qed.

lemma O_to_sub_O: ∀s1,s2. O s2 s1 → O s1 ⊆ O s2.
#s1 #s2 #H #g #Hg @(O_trans … H) // qed. 

lemma le_to_O: ∀s1,s2. (∀x.s1 x ≤ s2 x) → O s2 s1.
#s1 #s2 #Hle %{1} %{0} #n #_ normalize <plus_n_O @Hle
qed.

definition sum_f ≝ λf,g:nat→nat.λn.f n + g n.
interpretation "function sum" 'plus f g = (sum_f f g).

lemma O_plus: ∀f,g,s. O s f → O s g → O s (f+g).
#f #g #s * #cf * #nf #Hf * #cg * #ng #Hg
%{(cf+cg)} %{(max nf ng)} #n #Hmax normalize 
>distributive_times_plus_r @le_plus 
  [@Hf @(le_maxl … Hmax) |@Hg @(le_maxr … Hmax) ]
qed.
 
lemma O_plus_l: ∀f,s1,s2. O s1 f → O (s1+s2) f.
#f #s1 #s2 * #c * #a #Os1f %{c} %{a} #n #lean 
@(transitive_le … (Os1f n lean)) @le_times //
qed.

lemma O_plus_r: ∀f,s1,s2. O s2 f → O (s1+s2) f.
#f #s1 #s2 * #c * #a #Os1f %{c} %{a} #n #lean 
@(transitive_le … (Os1f n lean)) @le_times //
qed.

lemma O_absorbl: ∀f,g,s. O s f → O f g → O s (g+f).
#f #g #s #Osf #Ofg @(O_plus … Osf) @(O_trans … Osf) //
qed.

lemma O_absorbr: ∀f,g,s. O s f → O f g → O s (f+g).
#f #g #s #Osf #Ofg @(O_plus … Osf) @(O_trans … Osf) //
qed.

lemma O_times_c: ∀f,c. O f (λx:ℕ.c*f x).
#f #c %{c} %{0} //
qed.

lemma O_ext2: ∀f,g,s. O s f → (∀x.f x = g x) → O s g.
#f #g #s * #c * #a #Osf #eqfg %{c} %{a} #n #lean <eqfg @Osf //
qed.    


definition not_O ≝ λf,g.∀c,n0.∃n. n0 ≤ n ∧ c* (f n) < g n .

(* this is the only classical result *)
axiom not_O_def: ∀f,g. ¬ O f g → not_O f g.

(******************************* small O notation *****************************)

(*  o f g means g ∈ o(f) *)
definition o: relation (nat→nat) ≝
  λf,g.∀c.∃n0.∀n. n0 ≤ n → c * (g n) < f n.
  
lemma o_irrefl: ∀s. ¬ o s s.
#s % #oss cases (oss 1) #n0 #H @(absurd ? (le_n (s n0))) 
@lt_to_not_le >(times_n_1 (s n0)) in ⊢ (?%?); >commutative_times @H //
qed.

lemma o_trans: ∀s1,s2,s3. o s2 s1 → o s3 s2 → o s3 s1. 
#s1 #s2 #s3 #H1 #H2 #c cases (H1 c) #n1 -H1 #H1 cases (H2 1) #n2 -H2 #H2
%{(max n1 n2)} #n #Hmax 
@(transitive_lt … (H1 ??)) [@(le_maxl … Hmax)]
>(times_n_1 (s2 n)) in ⊢ (?%?); >commutative_times @H2 @(le_maxr … Hmax)
qed.
