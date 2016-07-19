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

(* maximization *)

let rec max' i f d ≝
  match i with 
  [ O ⇒ d
  | S j ⇒ 
      match (f j) with 
      [ true ⇒ j
      | false ⇒ max' j f d]].
      
definition max ≝ λn.λf.max' n f O.

theorem max_O: ∀f. max O f = O.
// qed.

theorem max_cases: ∀f.∀n.
  (f n = true ∧ max (S n) f = n) ∨ 
  (f n  = false ∧ max (S n) f = max n f).
#f #n normalize cases (f n) normalize /3/ qed.

theorem le_max_n: ∀f.∀n. max n f ≤ n.
#f #n (elim n) // #m #Hind 
normalize (cases (f m)) normalize @le_S // 
(* non trova Hind *)
@Hind
qed.

theorem lt_max_n : ∀f.∀n. O < n → max n f < n.
#f #n #posn @(lt_O_n_elim ? posn) #m
normalize (cases (f m)) normalize @le_S_S //
@le_max_n qed.

theorem le_to_le_max : ∀f.∀n,m.
n ≤ m  → max n f ≤ max m f.
#f #n #m #H (elim H) //
#i #leni #Hind @(transitive_le … Hind)
(cases (max_cases f i)) * #_ /2/ 
qed.

theorem true_to_le_max: ∀f.∀n,m.
 m < n → f m = true → m ≤ max n f.
#f #n (elim n)
  [#m #ltmO @False_ind /2/
  |#i #Hind #m #ltm 
   (cases (le_to_or_lt_eq … (le_S_S_to_le … ltm)))
    [#ltm #fm @(transitive_le ? (max i f)) 
      [@Hind /2/ | @le_to_le_max //]
    |#eqm >eqm #eqf normalize >eqf //
 ] 
qed.

theorem lt_max_to_false: ∀f.∀n,m.
 m < n → max n f < m → f m = false.
#f #n #m #ltnm #eqf cases(true_or_false (f m)) //
#fm @False_ind @(absurd … eqf) @(le_to_not_lt) @true_to_le_max //
qed.

lemma max_exists: ∀f.∀n,m.m < n → f m =true →
 (∀i. m < i → i < n → f i = false) → max n f = m.
#f #n (elim n) #m
  [#ltO @False_ind /2/ 
  |#Hind #max #ltmax #fmax #ismax
   cases (le_to_or_lt_eq …(le_S_S_to_le …(ltmax …)))
   #ltm normalize 
     [>(ismax m …) // normalize @(Hind max ltm fmax)
      #i #Hl #Hr @ismax // @le_S //
     |<ltm >fmax // 
     ]
   ]
qed.

lemma max_not_exists: ∀f.∀n.
 (∀i. i < n → f i = false) → max n f = O.
#f #n #ffalse @(le_gen ? n) #i (elim i) // #j #Hind #ltj
normalize >ffalse // @Hind /2/
qed.

lemma fmax_false: ∀f.∀n,m.max n f = m → f m = false → m = O. 
#f #n #m (elim n) //
#i #Hind normalize cases(true_or_false … (f i)) #fi >fi
normalize 
  [#eqm #fm @False_ind @(absurd … fi) // |@Hind]
qed. 
  
inductive max_spec (n:nat) (f:nat→bool) : nat→Prop ≝
 | found : ∀m:nat.m < n → f m =true →
 (∀i. m < i → i < n → f i = false) → max_spec n f m
 | not_found: (∀i.i < n → f i = false) → max_spec n f O.
 
theorem max_spec_to_max: ∀f.∀n,m.
  max_spec n f m → max n f = m.
#f #n #m #spec (cases spec) 
  [#max #ltmax #fmax #ismax @max_exists // @ismax
  |#ffalse @max_not_exists @ffalse
  ] 
qed.

theorem max_to_max_spec: ∀f.∀n,m.
  max n f = m → max_spec n f m.
#f #n #m (cases n)
  [#eqm <eqm %2 #i #ltiO @False_ind /2/ 
  |#n #eqm cases(true_or_false (f m)) #fm
    (* non trova max_to_false *)
    [%1 /2/
    |lapply (fmax_false ??? eqm fm) #eqmO >eqmO
     %2 #i (cases i) // #j #ltj @(lt_max_to_false … ltj) //
qed.

theorem max_f_g: ∀f,g,n.(∀i. i < n → f i = g i) → 
  max n f = max n g.
#f #g #n (elim n) //
#m #Hind #ext normalize >ext normalize in Hind; >Hind //
#i #ltim @ext @le_S //
qed.

theorem le_max_f_max_g: ∀f,g,n. (∀i. i < n → f i = true → g i =true) →
max n f ≤ max n g.
#f #g #n (elim n) //
#m #Hind #ext normalize (cases (true_or_false (f m))) #Heq >Heq 
  [>ext //
  |(cases (g m)) normalize [@le_max_n] @Hind #i #ltim @ext @le_S //
qed.

theorem f_max_true : ∀ f.∀n.
(∃i:nat. i < n ∧ f i = true) → f (max n f) = true. 
#f #n cases(max_to_max_spec f n (max n f) (refl …)) //
#Hall * #x * #ltx #fx @False_ind @(absurd … fx) >Hall /2/
qed.

theorem f_false_to_le_max: ∀f,n,p. (∃i:nat.i<n∧f i=true) →
  (∀m. p < m → f m = false) → max n f ≤ p.
#f #n #p #H1 #H2 @not_lt_to_le % #H3
@(absurd ?? not_eq_true_false) <(H2 ? H3) @sym_eq
@(f_max_true ? n H1)
qed.

theorem exists_forall_lt:∀f,n. 
(∃i. i < n ∧ f i = true) ∨ (∀i. i < n → f i = false).
#f #n elim n
  [%2 #i #lti0 @False_ind @(absurd ? lti0) @le_to_not_lt // 
  |#n1 *
    [* #a * #Ha1 #Ha2 %1 %{a} % // @le_S //
    |#H cases (true_or_false (f n1)) #HfS >HfS
      [%1 %{n1} /2/
      |%2 #i #lei 
       cases (le_to_or_lt_eq ?? lei) #Hi 
        [@H @le_S_S_to_le @Hi | destruct (Hi) //] 
      ]
    ]
  ]
qed.
     
theorem exists_max_forall_false:∀f,n. 
((∃i. i < n ∧ f i = true) ∧ (f (max n f) = true))∨
((∀i. i < n → f i = false) ∧ (max n f) = O).
#f #n
cases (exists_forall_lt f n)
  [#H %1 % // @(f_max_true f n) @H
  |#H %2 % [@H | @max_not_exists @H 
  ]
qed.


theorem false_to_lt_max: ∀f,n,m.O < n →
  f n = false → max m f ≤ n → max m f < n.
#f #n #m #posn #Hfn #Hmax cases (le_to_or_lt_eq ?? Hmax) -Hmax #Hmax 
  [//
  |cases (exists_max_forall_false f m)
    [* #_ #Hfmax @False_ind @(absurd ?? not_eq_true_false) //
    |* //
    ]
  ]
qed.

(* minimization *)
 
(* min k b f is the minimun i, b ≤ i < b + k s.t. f i;  
   returns  b + k otherwise *)
   
let rec min k b f ≝
  match k with
  [ O ⇒ b
  | S p ⇒ 
    match f b with
   [ true ⇒ b
   | false ⇒ min p (S b) f]].

definition min0 ≝ λn.λf. min n 0 f.

theorem min_O_f : ∀f.∀b. min O b f = b.
// qed.

theorem true_min: ∀f.∀b.
  f b = true → ∀n.min n b f = b.
#f #b #fb #n (cases n) // #n normalize >fb normalize //
qed.

theorem false_min: ∀f.∀n,b.
  f b = false → min (S n) b f = min n (S b) f.
#f #n #b #fb normalize >fb normalize //
qed.

(*
theorem leb_to_le_min : ∀f.∀n,b1,b2.
b1 ≤ b2  → min n b1 f ≤ min n b2 f.
#f #n #b1 #b2 #leb (elim n) //
#m #Hind normalize (cases (f m)) normalize *)

theorem le_min_r: ∀f.∀n,b. min n b f ≤ n + b.
#f #n normalize (elim n) // #m #Hind #b 
normalize (cases (f b)) normalize // 
qed.

theorem le_min_l: ∀f.∀n,b. b ≤ min n b f.
#f #n normalize (elim n) // #m #Hind #b 
normalize (cases (f b)) normalize /2/ 
qed.

theorem le_to_le_min : ∀f.∀n,m.
n ≤ m  → ∀b.min n b f ≤ min m b f.
#f @nat_elim2 //
  [#n #leSO @False_ind /2/ 
  |#n #m #Hind #leSS #b
   (cases (true_or_false (f b))) #fb 
    [lapply (true_min …fb) #H >H >H //
    |>false_min // >false_min // @Hind /2/
    ]
  ]
qed.

theorem true_to_le_min: ∀f.∀n,m,b.
 b ≤ m → f m = true → min n b f ≤ m.
#f #n (elim n) //
#i #Hind #m #b #leb (cases (le_to_or_lt_eq … leb))
  [#ltm #fm normalize (cases (f b)) normalize // @Hind //
  |#eqm <eqm #eqb normalize >eqb normalize //
  ] 
qed.

theorem lt_min_to_false: ∀f.∀n,m,b. 
 b ≤ m → m < min n b f → f m = false.
#f #n #m #b #lebm #ltm cases(true_or_false (f m)) //
#fm @False_ind @(absurd … ltm) @(le_to_not_lt) @true_to_le_min //
qed.

theorem fmin_true: ∀f.∀n,m,b.
 m = min n b f → m < n + b → f m = true. 
#f #n (elim n)
  [#m #b normalize #eqmb >eqmb #leSb @(False_ind) 
   @(absurd … leSb) //
  |#n #Hind #m #b (cases (true_or_false (f b))) #caseb
    [>true_min //
    |>false_min // #eqm #ltm @(Hind m (S b)) /2/
    ]
  ]
qed.

lemma min_exists: ∀f.∀t,m. m < t → f m = true →
∀k,b.b ≤ m → (∀i. b ≤ i → i < m → f i = false) → t = k + b → 
  min k b f = m. 
#f #t #m #ltmt #fm #k (elim k)
  [#b #lebm #ismin #eqtb @False_ind @(absurd … lebm) <eqtb
   @lt_to_not_le //
  |#d #Hind #b #lebm #ismin #eqt cases(le_to_or_lt_eq …lebm)
    [#ltbm >false_min /2 by le_n/ @Hind //
      [#i #H #H1 @ismin /2/ | >eqt normalize //] 
    |#eqbm >true_min //
    ]
  ]
qed.

lemma min_not_exists: ∀f.∀n,b.
 (∀i. b ≤ i → i < n + b → f i = false) → min n b f = n + b.
#f #n (elim n) // 
#p #Hind #b #ffalse >false_min
  [>Hind // #i #H #H1 @ffalse /2/
  |@ffalse //
  ]
qed.

lemma fmin_false: ∀f.∀n,b.let m ≝ min n b f in 
 f m = false → m = n+b. 
#f #n (elim n) //
#i #Hind #b normalize cases(true_or_false … (f b)) #fb >fb
normalize 
  [#eqm @False_ind @(absurd … fb) // 
  |>plus_n_Sm @Hind]
qed.

inductive min_spec (n,b:nat) (f:nat→bool) : nat→Prop ≝
 | found : ∀m:nat. b ≤ m → m < n + b → f m =true →
 (∀i. b ≤ i → i < m → f i = false) → min_spec n b f m
 | not_found: (∀i.b ≤ i → i < (n + b) → f i = false) → min_spec n b f (n+b).
 
theorem min_spec_to_min: ∀f.∀n,b,m.
  min_spec n b f m → min n b f = m.
#f #n #b #m #spec (cases spec) 
  [#m #lem #ltm #fm #ismin @(min_exists f (n+b)) // @ismin
  |#ffalse @min_not_exists @ffalse
  ] 
qed.

theorem min_to_min_spec: ∀f.∀n,b,m.
  min n b f = m → min_spec n b f m.
#f #n #b #m (cases n)
  [#eqm <eqm %2 #i #lei #lti @False_ind @(absurd … lti) /2/
  |#n #eqm (* (cases (le_to_or_lt_eq … (le_min_r …))) Stack overflow! *)
   lapply (le_min_r f (S n) b) >eqm #lem
   (cases (le_to_or_lt_eq … lem)) #mcase
    [%1 /2/ #i #H #H1 @(lt_min_to_false f (S n) i b) //
    |>mcase %2 #i #lebi #lti @(lt_min_to_false f (S n) i b) //
    ]
  ]
qed.

theorem min_f_g: ∀f,g,n,b.(∀i. b ≤ i → i < n + b → f i = g i) → 
  min n b f = min n b g.
#f #g #n (elim n) //
#m #Hind #b #ext normalize >(ext b (le_n b) ?) // >Hind //
#i #ltib #ltim @ext // @lt_to_le //
qed.

theorem le_min_f_min_g: ∀f,g,n,b. (∀i. b ≤ i → i < n +b → f i = true → g i =true) →
min n b g ≤ min n b f.
#f #g #n (elim n) //
#m #Hind #b #ext normalize (cases (true_or_false (f b))) #Heq >Heq 
  [>ext //
  |(cases (g b)) normalize /2 by lt_to_le/ @Hind #i #ltb #ltim #fi
    @ext /2/
  ]
qed.

theorem f_min_true : ∀ f.∀n,b.
(∃i:nat. b ≤ i ∧ i < n + b ∧ f i = true) → f (min n b f) = true. 
#f #n #b cases(min_to_min_spec f n b (min n b f) (refl …)) //
#Hall * #x * * #leb #ltx #fx @False_ind @(absurd … fx) >Hall /2/
qed.

theorem lt_min : ∀ f.∀n,b.
(∃i:nat. b ≤ i ∧ i < n + b ∧ f i = true) → min n b f < n + b. 
#f #n #b #H cases H #i * * #lebi #ltin #fi_true  
@(le_to_lt_to_lt … ltin) @true_to_le_min //
qed.