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

include "arithmetics/primes.ma".
  
let rec gcd_aux p m n: nat ≝
match p with 
  [O ⇒ m
  |S q ⇒ 
    match dividesb n m with
    [ true ⇒ n
    | false ⇒ gcd_aux q n (m \mod n)]].
    
definition gcd : nat → nat → nat ≝ λn,m:nat.
  match leb n m with
  [ true ⇒ gcd_aux n m n 
  | false ⇒ gcd_aux m n m ].
  
theorem commutative_gcd: ∀n,m. gcd n m = gcd m n.
#n #m normalize @leb_elim 
  [#lenm cases(le_to_or_lt_eq … lenm)
    [#ltnm >not_le_to_leb_false // @lt_to_not_le //
    |#eqnm >eqnm (cases (leb m m)) //
    ]
  |#notlenm >le_to_leb_true // @(transitive_le ? (S m)) //
   @not_le_to_lt //
  ]
qed.

theorem gcd_O_l: ∀m. gcd O m = m. 
// qed.  
  
theorem divides_mod: ∀p,m,n:nat. O < n → 
  p ∣ m → p ∣ n → p ∣ (m \mod n).
#p #m #n #posn * #qm #eqm * #qn #eqn
@(quotient ?? (qm - qn*(m / n))) >distributive_times_minus
<eqm <associative_times <eqn @sym_eq @plus_to_minus /2/
qed.

theorem divides_mod_to_divides: ∀p,m,n:nat. O < n →
  p ∣ (m \mod n) → p ∣ n → p ∣ m.
#p #m #n #posn * #q1 #eq1 * #q2 #eq2
@(quotient p m ((q2*(m / n))+q1)) >distributive_times_plus
<eq1 <associative_times <eq2 /2/
qed.

lemma divides_to_gcd_aux: ∀p,m,n. O < p → O < n →n ∣ m → 
  gcd_aux p m n = n.
#p #m #n #posp @(lt_O_n_elim … posp) #l #posn #divnm whd in ⊢ (??%?);
>divides_to_dividesb_true normalize //
qed.

theorem divides_to_gcd: ∀m,n. O < n → n ∣ m → 
  gcd n m = n.
#m #n #posn (cases m)
 [>commutative_gcd //
 |#l #divn (cut (n ≤ (S l))) [@divides_to_le //] #len normalize
  >le_to_leb_true // normalize @divides_to_gcd_aux //
 ]
qed.

lemma not_divides_to_gcd_aux: ∀p,m,n. 0 < n → n ∤ m → 
  gcd_aux (S p) m n = gcd_aux p n (m \mod n).
#p #m #n #lenm #divnm whd in ⊢ (??%?); >not_divides_to_dividesb_false
normalize // qed.

theorem divides_gcd_aux_mn: ∀p,m,n. O < n → n ≤ m → n ≤ p →
  gcd_aux p m n ∣ m ∧ gcd_aux p m n ∣ n. 
#p (elim p)
  [#m #n #posn #lenm #lenO @False_ind @(absurd … posn) /2/
  |#q #Hind #m #n #posn #lenm #lenS cases(decidable_divides n m)
    [#divnm >(divides_to_gcd_aux … posn divnm) // % //
    |#ndivnm >(not_divides_to_gcd_aux … posn ndivnm)
     cut (gcd_aux q n (m \mod n) ∣ n ∧
          gcd_aux q n (m \mod n) ∣ mod m n)
      [cut (m \mod n < n) [@lt_mod_m_m //] #ltmod
       @Hind
        [cases(le_to_or_lt_eq … (le_O_n (m \mod n))) // #modO
         @False_ind @(absurd ?? ndivnm) @mod_O_to_divides //
        |/2/
        |@le_S_S_to_le @(transitive_le … ltmod lenS)
        ]
      |* #H #H1 % [@(divides_mod_to_divides … posn H1) // |//]
      ]
    ]
  ]
qed.

theorem divides_gcd_nm: ∀n,m.
  gcd n m ∣ m ∧ gcd n m ∣ n.
#n #m cases(le_to_or_lt_eq …(le_O_n n)) [|#eqnO <eqnO /2/]
#posn cases(le_to_or_lt_eq …(le_O_n m)) [|#eqmO <eqmO /2/]
#posm normalize @leb_elim normalize  
  [#lenm @divides_gcd_aux_mn //
  |#notlt normalize cut (∀A,B. A∧B → B∧A) [#A #B * /2/] #sym_and
   @sym_and @divides_gcd_aux_mn // @(transitive_le ? (S m)) //
   @not_le_to_lt //
  ]
qed. 

theorem divides_gcd_l: ∀n,m. gcd n m ∣ n.
#n #m @(proj2  ? ? (divides_gcd_nm n m)).
qed.

theorem divides_gcd_r: \forall n,m. gcd n m ∣ m.
#n #m @(proj1 ? ? (divides_gcd_nm n m)).
qed.

theorem divides_times_gcd_aux: ∀p,m,n,d,c. 
  O < c → O < n → n ≤ m → n ≤ p →
    d ∣ (c*m) → d ∣ (c*n) → d ∣ c*gcd_aux p m n. 
#p (elim p) 
  [#m #n #d #c #_ #posn #_ #lenO @False_ind @(absurd … lenO) /2/
  |#q #Hind #m #n #d #c #posc #posn #lenm #lenS #dcm #dcn
   cases(decidable_divides n m)
    [#divnm >(divides_to_gcd_aux … posn divnm) //
    |#ndivnm >(not_divides_to_gcd_aux … posn ndivnm)
     cut (m \mod n < n) [@lt_mod_m_m //] #ltmod
     @Hind //
      [cases(le_to_or_lt_eq … (le_O_n (m \mod n))) // #modO
       @False_ind @(absurd ?? ndivnm) @mod_O_to_divides //
      |/2/
      |@le_S_S_to_le @(transitive_le … ltmod lenS)
      |<times_mod // < (commutative_times c m)
       <(commutative_times c n) @divides_mod //
       >(times_n_O 0) @lt_times //
      ]
    ]
  ]
qed. 

(*a particular case of the previous theorem, with c=1 *)
theorem divides_gcd_aux: ∀p,m,n,d. O < n → n ≤ m → n ≤ p →
  d ∣ m \to d ∣ n \to d ∣ gcd_aux p m n.
  (* bell'esempio di smart application *)
/2/ qed. 

theorem divides_d_times_gcd: ∀m,n,d,c. O < c → 
  d ∣ (c*m) → d ∣ (c*n) → d ∣ c*gcd n m. 
#m #n #d #c #posc #dcm #dcn 
cases(le_to_or_lt_eq …(le_O_n n)) [|#eqnO <eqnO @dcm] #posn 
cases(le_to_or_lt_eq …(le_O_n m)) [|#eqmO <eqmO <commutative_gcd @dcn] #posm
normalize @leb_elim normalize
  [#lenm @divides_times_gcd_aux //
  |#nlenm @divides_times_gcd_aux //
   @(transitive_le ? (S m)) // @not_le_to_lt //
  ]
qed.

(* a particular case of the previous theorem, with c=1 *)
theorem divides_d_gcd: ∀m,n,d. 
 d ∣ m → d ∣ n → d ∣ gcd n m.
#m #n #d #divdn #divdn applyS (divides_d_times_gcd m n d 1) //
qed.

theorem eq_minus_gcd_aux: ∀p,m,n.O < n → n ≤ m →  n ≤ p →
  ∃a,b. a*n - b*m = gcd_aux p m n ∨ b*m - a*n = gcd_aux p m n.
#p (elim p)
  [#m #n #posn #lenm #lenO @False_ind @(absurd … posn) /2/
  |#q #Hind #m #n #posn #lenm #lenS 
   cut (0 < m) [@lt_to_le_to_lt //] #posm 
   cases(decidable_divides n m)
    [#divnm >(divides_to_gcd_aux … posn divnm) // 
     @(ex_intro ?? 1) @(ex_intro ?? 0) %1 //
    |#ndivnm >(not_divides_to_gcd_aux … posn ndivnm)
     cut (m \mod n < n) [@lt_mod_m_m //] #ltmod
     lapply (Hind n (m \mod n) ???)
      [@le_S_S_to_le @(transitive_le … ltmod lenS)
      |/2/
      |cases(le_to_or_lt_eq … (le_O_n (m \mod n))) // #modO
       @False_ind @(absurd ?? ndivnm) @mod_O_to_divides //
      ]
     * #a * #b * #H
      [(* first case *)
       <H @(ex_intro ?? (b+a*(m / n))) @(ex_intro ?? a) %2
       <commutative_plus >distributive_times_plus_r 
       >(div_mod m n) in ⊢(? ? (? % ?) ?);
       >associative_times <commutative_plus >distributive_times_plus
       <minus_plus <commutative_plus <plus_minus //
      |(* second case *)
        <H @(ex_intro ?? (b+a*(m / n))) @(ex_intro ?? a) %1
        >distributive_times_plus_r
        >(div_mod m n) in ⊢ (? ? (? ? %) ?);
        >distributive_times_plus >associative_times
        <minus_plus <commutative_plus <plus_minus //
      ]
    ]
  ]
qed.

theorem eq_minus_gcd:
  ∀m,n.∃ a,b.a*n - b*m = gcd n m ∨ b*m - a*n = gcd n m.
  #m #n cases(le_to_or_lt_eq …(le_O_n n)) 
  [|#eqn0 >eqn0 @(ex_intro ?? O) @(ex_intro ? ? 1) %2 applyS minus_n_O]
#posn cases(le_to_or_lt_eq …(le_O_n m)) 
  [|#eqm0 >eqm0 @(ex_intro ?? 1) @(ex_intro ? ? 0) %1 applyS minus_n_O]
#posm normalize @leb_elim normalize
  [#lenm @eq_minus_gcd_aux //
  |#nlenm lapply(eq_minus_gcd_aux m n m posm ? (le_n m))
    [@(transitive_le … (not_le_to_lt … nlenm)) //]
   * #a * #b * #H @(ex_intro ?? b) @(ex_intro ?? a) [%2 // |%1 //]
  ]
qed.

(* some properties of gcd *)

theorem gcd_O_to_eq_O:∀m,n:nat. 
  gcd m n = O → m = O ∧ n = O.
#m #n #H cut (O ∣ n ∧ O ∣ m)
  [<H @divides_gcd_nm| * * #q1 #H1 * #q2 #H2 % // ]
qed.

theorem lt_O_gcd:∀m,n:nat. O < n → O < gcd m n.
#m #n #posn @(nat_case (gcd m n)) // 
#H (cases (gcd_O_to_eq_O m n H)) //
qed.

theorem gcd_n_n: ∀n.gcd n n = n.
#n (cases n) //
#m @le_to_le_to_eq
  [@divides_to_le //
  |@divides_to_le (*/2/*) [@lt_O_gcd // |@divides_d_gcd // ]
  ]
qed.

(* some properties or relative primes - i.e. gcd = 1 *)
theorem gcd_1_to_lt_O: ∀i,n. 1 < n → gcd i n = 1 → O < i.
#i #n #lt1n #gcd1 cases (le_to_or_lt_eq ?? (le_O_n i)) //
#iO @False_ind @(absurd … gcd1) <iO normalize
@sym_not_eq @lt_to_not_eq //
qed.

theorem gcd_1_to_lt_n: ∀i,n. 1 < n → 
  i ≤ n → gcd i n = 1 → i < n.
#i #n #lt1n #lein #gcd1 cases (le_to_or_lt_eq ?? lein) //
(* impressive *)
qed.

theorem  gcd_n_times_nm: ∀n,m. O < m → gcd n (n*m) = n.
#n #m #posm @(nat_case n) //
#l #eqn @le_to_le_to_eq
  [@divides_to_le //
  |@divides_to_le
    [@lt_O_gcd >(times_n_O O) @lt_times // |@divides_d_gcd /2/]
  ]
qed.

theorem le_gcd_times: ∀m,n,p. O< p → gcd m n ≤ gcd m (n*p).
#m #n #p #posp @(nat_case n) // 
#l #eqn @divides_to_le [@lt_O_gcd >(times_n_O O) @lt_times //] 
@divides_d_gcd [@(transitive_divides ? (S l)) /2/ |//]
qed.

theorem gcd_times_SO_to_gcd_SO: ∀m,n,p:nat. O < n → O < p → 
  gcd m (n*p) = 1 → gcd m n = 1.
#m #n #p #posn #posp #gcd1 @le_to_le_to_eq
  [<gcd1 @le_gcd_times // | @lt_O_gcd //]
qed.

(* for the "converse" of the previous result see the end  of this development *)

theorem eq_gcd_SO_to_not_divides: ∀n,m. 1 < n → 
  gcd n m = 1 → n ∤ m.
#n #m #lt1n #gcd1 @(not_to_not … (gcd n m = n))
  [#divnm @divides_to_gcd /2/ | /2/]
qed.

theorem gcd_SO_n: ∀n:nat. gcd 1 n = 1.
#n @le_to_le_to_eq
  [@divides_to_le // |>commutative_gcd @lt_O_gcd //]
qed.

theorem divides_gcd_mod: ∀m,n:nat. O < n →
  gcd m n ∣ gcd n (m \mod n).
#m #n #posn @divides_d_gcd [@divides_mod // | //]
qed.

theorem divides_mod_gcd: ∀m,n:nat. O < n →
  gcd n (m \mod n) ∣ gcd m n.
#m #n #posn @divides_d_gcd
  [@divides_gcd_l |@(divides_mod_to_divides ?? n) //]
qed.

theorem gcd_mod: ∀m,n:nat. O < n →
  gcd n (m \mod n) = gcd m n.
#m #n #posn @antisymmetric_divides
  [@divides_mod_gcd // | @divides_gcd_mod //]
qed.

(* gcd and primes *)

theorem prime_to_gcd_1: ∀n,m:nat. prime n → n ∤ m →
  gcd n m = 1.
(* bella dimostrazione *)
#n #m * #lt1n #primen #ndivnm @le_to_le_to_eq
  [@not_lt_to_le @(not_to_not … (primen (gcd n m) (divides_gcd_l …)))
   @(not_to_not ? (n ∣m)) //
  |@lt_O_gcd @not_eq_to_le_to_lt // @(not_to_not ? (n ∣ m)) //
  ]
qed.

(* primes and divides *)
theorem divides_times_to_divides: ∀p,n,m:nat.prime p → 
  p ∣ n*m → p ∣ n ∨ p ∣ m.
#p #n #m #primp * #c #nm
cases (decidable_divides p n) /2/ #ndivpn %2 
cut (∃a,b. a*n - b*p = 1 ∨ b*p - a*n = 1)
  [<(prime_to_gcd_1 … primp ndivpn) >commutative_gcd @eq_minus_gcd]
* #a * #b * #H
  [@(quotient ?? (a*c-b*m)) >distributive_times_minus <associative_times 
   >(commutative_times p) >associative_times <nm <associative_times
   <associative_times <commutative_times >(commutative_times (p*b))
   <distributive_times_minus //
  |@(quotient ?? (b*m -a*c)) >distributive_times_minus <(associative_times p)
   <(associative_times p) <(commutative_times a) >(associative_times a)
   <nm <(associative_times a) <commutative_times >(commutative_times (a*n))
   <distributive_times_minus //
  ]
qed.

theorem divides_exp_to_divides: 
∀p,n,m:nat. prime p → p ∣n^m → p ∣ n.
#p #n #m #primep (elim m) normalize /2/
#l #Hind #H cases(divides_times_to_divides  … primep H) /2/
qed.

theorem divides_exp_to_eq: 
∀p,q,m:nat. prime p → prime q →
  p ∣ q^m → p = q.
#p #q #m #H * #lt1q #primeq #H @primeq /2/
qed.

(* relative primes *)
theorem eq_gcd_times_1: ∀p,n,m:nat. O < n → O < m →
 gcd p n = 1 → gcd p m = 1 → gcd p (n*m) = 1.
#p #n #m #posn #posm #primepn #primepm 
@le_to_le_to_eq [|@lt_O_gcd >(times_n_O 0) @lt_times //]
@not_lt_to_le % #lt1gcd
cut (smallest_factor (gcd p (n*m)) ∣ n ∨ 
     smallest_factor (gcd p (n*m)) ∣ m)
  [@divides_times_to_divides
    [@prime_smallest_factor_n //
    |@(transitive_divides ? (gcd p (n*m))) // 
     @divides_smallest_factor_n /2/
    ]
  |* #H
    [@(absurd ?? (lt_to_not_le …(lt_SO_smallest_factor … lt1gcd)))
     <primepn @divides_to_le // @divides_d_gcd //
     @(transitive_divides … (divides_smallest_factor_n …))
       [@lt_O_gcd >(times_n_O 0) @lt_times // | //]
    |@(absurd ?? (lt_to_not_le … (lt_SO_smallest_factor …lt1gcd)))
     <primepm @divides_to_le // @divides_d_gcd //
     @(transitive_divides … (divides_smallest_factor_n …))
       [@lt_O_gcd >(times_n_O 0) @lt_times // | //]
  ]
qed.


theorem gcd_1_to_divides_times_to_divides: ∀p,n,m:nat. O < p →
gcd p n = 1 → p ∣ (n*m) → p ∣ m.
#p #m #n #posn #gcd1 * #c #nm
cases(eq_minus_gcd m p) #a * #b * #H >gcd1 in H; #H 
  [@(quotient ?? (a*n-c*b)) >distributive_times_minus <associative_times 
   <associative_times <nm >(commutative_times m) >commutative_times
   >associative_times <distributive_times_minus //
  |@(quotient ?? (c*b-a*n)) >distributive_times_minus <associative_times 
   <associative_times <nm >(commutative_times m) <(commutative_times n)
   >associative_times <distributive_times_minus //
  ]
qed.

(*
theorem divides_to_divides_times1: \forall p,q,n. prime p \to prime q \to p \neq q \to
divides p n \to divides q n \to divides (p*q) n.
intros.elim H3.
rewrite > H5 in H4.
elim (divides_times_to_divides ? ? ? H1 H4)
  [elim H.apply False_ind.
   apply H2.apply sym_eq.apply H8
    [assumption
    |apply prime_to_lt_SO.assumption
    ]
  |elim H6.
   apply (witness ? ? n1).
   rewrite > assoc_times.
   rewrite < H7.assumption
  ]
qed.
*)

theorem divides_to_divides_times: ∀p,q,n. prime p  → p ∤ q →
 p ∣ n → q ∣ n → p*q ∣ n.
#p #q #n #primep #notdivpq #divpn * #b #eqn >eqn in divpn;
#divpn cases(divides_times_to_divides ??? primep divpn) #H
  [@False_ind /2/ 
  |cases H #c #eqb @(quotient ?? c) >eqb <associative_times //
  ]
qed.