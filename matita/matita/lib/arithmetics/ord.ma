(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic   
    ||A||  Library of Mathematics, developed at the Computer Science 
    ||T||  Department of the University of Bologna, Italy.           
    ||I||                                                            
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_____________________________________________________________*)

include "arithmetics/exp.ma".
include "basics/types.ma".
include "arithmetics/primes.ma".
include "arithmetics/gcd.ma". 

let rec p_ord_aux p n m ≝
  match n \mod m with
  [ O ⇒ 
    match p with
      [ O ⇒ 〈O,n〉
      | S p ⇒ let 〈q,r〉 ≝ p_ord_aux p (n / m) m in 〈S q,r〉]
  | S a ⇒ 〈O,n〉].
 
(* p_ord n m = <q,r> if m divides n q times, with remainder r *)
definition p_ord ≝ λn,m:nat.p_ord_aux n n m.

lemma p_ord_aux_0: ∀n,m.p_ord_aux 0 n m = 〈0,n〉.
#n #m whd in match (p_ord_aux 0??); cases (n\mod m) normalize //
qed. 

lemma p_ord_aux_Strue: ∀n,m,p,q,r.
 n\mod m = 0 → p_ord_aux p (n / m) m = 〈q,r〉 →
 p_ord_aux (S p) n m = 〈S q,r〉.
#n #m #p #q #r whd in match (p_ord_aux (S p)??); #H >H 
#Hord whd in ⊢(??%?); >Hord //
qed. 

lemma p_ord_aux_false: ∀p,n,m,a.
 n\mod m = (S a) → p_ord_aux p n m = 〈0,n〉.
#p #n #m #a cases p whd in match (p_ord_aux ???); 
  [#H whd in match (p_ord_aux ???); >H // 
  |#p1 #H whd in match (p_ord_aux ???); >H //
  ] 
qed. 

(* the definition of p_ord_aux only makes sense for m>1. 
   In case m=1 we always end up with the pair 〈p,n〉 *)

lemma p_ord_degenerate: ∀p,n. p_ord_aux p n 1 = 〈p,n〉.
#p elim p // #p1 #Hind #n
cut (mod n 1 = 0) [@divides_to_mod_O //] #Hmod
>(p_ord_aux_Strue … (Hind … ) ) // >(div_mod n 1) in ⊢ (???%); //
qed.

theorem p_ord_aux_to_exp: ∀p,n,m,q,r. O < m →
  p_ord_aux p n m = 〈q,r〉 → n = m \sup q *r .
#p elim p
  [#n #m @(nat_case (n \mod m))
    [#Hmod #q #r #posm >p_ord_aux_0 #Hqr destruct (Hqr) //
    |#a #H #q #r #posm >(p_ord_aux_false … H) #Hqr destruct (Hqr) //
    ]
  |#p1 #Hind #n #m @(nat_case (n \mod m))
    [#Hmod #q #r #posm lapply (refl …(p_ord_aux p1 (n/m) m));
     cases (p_ord_aux p1 (n/m) m) in ⊢ (???%→?); #q1 #r1 #H1
     >(p_ord_aux_Strue … Hmod H1) #H destruct (H) whd in match (exp ??);
     >(div_mod n m) >Hmod <plus_n_O >(Hind … H1) //
    |#a #H #q #r #posm >(p_ord_aux_false … H) #Hqr destruct (Hqr) //
    ]
  ]
qed.

(* questo va spostato in primes1.ma *)
theorem p_ord_exp: ∀n,m,i. O < m → n \mod m ≠ O →
  ∀p. i ≤ p → p_ord_aux p (m \sup i * n) m = 〈i,n〉.
#n #m #i #posm #Hmod 
cut (∃a.n\mod m = S a)
  [@(nat_case (n\mod m)) [#H @False_ind /2/|#a #Hmod1 %{a} //]] * #mod1 #Hmod1
elim i
  [#p normalize #posp <plus_n_O @(p_ord_aux_false … Hmod1)
  |-i #i #Hind #p 
   @(nat_case p) [#Hp >Hp #Habs @False_ind @(absurd … Habs) //]
   #p1 #Hp1 #lep1
   cut (((m \sup (S i)*n) \mod m) = O)
    [whd in match (exp ??); @divides_to_mod_O // %{(m^i*n)} //] #Hmod2
   @(p_ord_aux_Strue … Hmod2) <(Hind p1) [2: @le_S_S_to_le //]
   @eq_f2 // whd in match (exp ??); >associative_times >(commutative_times m)
   <associative_times >div_times //
  ]
qed.

theorem p_ord_aux_to_not_mod_O: ∀p,n,m,q,r. 1<m → O<n → n≤p →
  p_ord_aux p n m = 〈q,r〉 → r \mod m ≠ O.
#p elim p
  [#n #m #q #r #_ #posn #nposn @False_ind @(absurd … posn) /2/  
  |#p1 #Hind #n #m @(nat_case (n \mod m))
    [#Hmod #q #r #lt1m #posn #len lapply (refl …(p_ord_aux p1 (n/m) m));
     cases (p_ord_aux p1 (n/m) m) in ⊢ (???%→?); #q1 #r1 #H1
     >(p_ord_aux_Strue … Hmod H1) #H destruct (H) whd in match (exp ??);
     @(Hind … lt1m … H1) 
      [@(pos_div … posn Hmod) @lt_to_le //
      |@le_S_S_to_le @(transitive_le … len) @lt_times_to_lt_div
       >(times_n_1 n) in ⊢ (?%?); @monotonic_lt_times_r //
      ]
    |#a #H #q #r #lt1m #posn #posm >(p_ord_aux_false … H) #Hqr destruct (Hqr)
     >H @sym_not_eq //
    ]
  ]
qed.

theorem p_ord_exp1: ∀p,n,q,r. O < p → p ∤ r →
  n = p \sup q * r → p_ord n p = 〈q,r〉.
#p #n #q #r #posp #ndivpr #Hn >Hn -Hn -n @(p_ord_exp … posp)
  [@(not_to_not … ndivpr) /2/
  |@(transitive_le ? (p \sup q))
    [cut (1<p) 
      [cases (le_to_or_lt_eq … posp) // #eqp1 @False_ind @(absurd ?? ndivpr)
       <eqp1 % //]
     #lt1p elim q // -q #q whd in match (exp ??);
     cases q [#_ normalize <plus_n_O @lt_to_le //]
     #q1 #Hind @(lt_to_le_to_lt ? ((S q1)*2))
      [>(times_n_1 (S q1)) in ⊢ (?%?); @monotonic_lt_times_r //
      |@le_times //
      ]
    |>(times_n_1 (p^q)) in ⊢ (?%?); @le_times // 
     lapply ndivpr -ndivpr cases r // #Habs @False_ind @(absurd ?? Habs) % //
    ]
  ]
qed.

theorem p_ord_to_exp1: ∀p,n,q,r. 1<p → O<n → p_ord n p = 〈q,r〉 → 
  p ∤ r ∧ n = p \sup q * r.
#p #n #q #r #lt1p #posn #Hord %
  [@(not_to_not … (p_ord_aux_to_not_mod_O … lt1p posn (le_n n)… Hord))
   @divides_to_mod_O @lt_to_le //
  |@(p_ord_aux_to_exp n …Hord) @lt_to_le //
  ]
qed.

theorem eq_p_ord_q_O: ∀p,n,q. p_ord n p = 〈q,O〉 → n=O ∧ q=O.
#p #n whd in match (p_ord ??);  cases n 
  [#q cases p normalize [|#q1] #H destruct (H) % //
  |#n1 #q cases p 
    [normalize #H destruct (H) 
    |#p1 cases p1
      [>p_ord_degenerate #H destruct (H)
      |#p2 lapply (refl …(p_ord_aux (S n1) (S n1) (S (S p2))));
       cases (p_ord_aux (S n1) (S n1) (S (S p2))) in ⊢ (???%→?); #qa #ra #H 
       lapply (p_ord_to_exp1 (S (S p2)) (S n1) … H) //
       * #_ #H1 >H #H2 @False_ind destruct (H2) <times_n_O in H1; 
       #Habs destruct (Habs)
      ]
    ]
  ]
qed.

theorem p_ord_times: ∀p,a,b,qa,ra,qb,rb. prime p → O < a → O < b 
 → p_ord a p = 〈qa,ra〉  → p_ord b p = 〈qb,rb〉
  → p_ord (a*b) p = 〈qa + qb, ra*rb〉.
#p #a #b #qa #ra #qb #rb #Hprime #posa #posb #porda #pordb 
cut (1<p) [@prime_to_lt_SO //] #Hp1
cases (p_ord_to_exp1 ???? Hp1 posa porda) -posa -porda #Hdiva #Ha
elim (p_ord_to_exp1 ???? Hp1 posb pordb) -posb -pordb #Hdivb #Hb
@p_ord_exp1 
  [@lt_to_le //
  |% #Hdiv cases (divides_times_to_divides ? ? ? Hprime Hdiv)
   #Habs @absurd /2/
  |>Ha >Hb -Ha -Hb // 
  ]
qed.

theorem fst_p_ord_times: ∀p,a,b. prime p → O < a → O < b → 
  fst ?? (p_ord (a*b) p) = (fst ?? (p_ord a p)) + (fst ?? (p_ord b p)).
#p #a #b #primep #posa #posb
>(p_ord_times p a b (fst ?? (p_ord a p)) (snd ?? (p_ord a p))
  (fst ?? (p_ord b p)) (snd ? ? (p_ord b p)) primep posa posb) //
qed.

theorem p_ord_p: ∀p:nat. 1 < p → p_ord p p = 〈1,1〉.
#p #ltp1 @p_ord_exp1
  [@lt_to_le //
  |% #divp1 @(absurd … ltp1) @le_to_not_lt @divides_to_le //
  |//
  ]
qed.

(* p_ord and divides *)
theorem divides_to_p_ord: ∀p,a,b,c,d,n,m:nat. O < n → O < m → prime p 
→ divides n m → p_ord n p = 〈a,b〉 →
  p_ord m p = 〈c,d〉 → divides b d ∧ a ≤ c.
#p #a #b #c #d #n #m #posn #posm #primep #divnm #ordn #ordm
cut (1<p) [@prime_to_lt_SO //] #Hposp
cases (p_ord_to_exp1 ? ? ? ? Hposp posn ordn) #divn #eqn
cases (p_ord_to_exp1 ? ? ? ? Hposp posm ordm) #divm #eqm %
  [@(gcd_1_to_divides_times_to_divides b (exp p c))
    [cases (le_to_or_lt_eq ?? (le_O_n b)) //
    |elim c 
      [>commutative_gcd //
      |#c0 #Hind @eq_gcd_times_1 
        [@lt_O_exp @lt_to_le //
        |@lt_to_le //
        |@Hind 
        |>commutative_gcd @prime_to_gcd_1 //
        ] 
      ]
    |@(transitive_divides ? n) [%{(exp p a)} // |<eqm //]
    ]
  |@(le_exp_to_le p) //
   @divides_to_le
    [@lt_O_exp @lt_to_le // 
    |@(gcd_1_to_divides_times_to_divides ? d)
      [@lt_O_exp @lt_to_le // 
      |elim a
        [@gcd_SO_n
        |#a0 #Hind whd in match (exp ??); 
         >commutative_gcd @eq_gcd_times_1
          [@lt_O_exp @lt_to_le // 
          |@lt_to_le //
          |/2/ 
          |>commutative_gcd @prime_to_gcd_1 //
          ]
        ]
      |@(transitive_divides ? n) // %{b} // 
      ]
    ]
  ]
qed.    

(* p_ord and primes *)
theorem not_divides_to_p_ord_O: ∀n,i.
  (nth_prime i) ∤ n → p_ord n (nth_prime i) = 〈O,n〉.
#n #i #H @p_ord_exp1 //
qed.

theorem p_ord_O_to_not_divides: ∀n,i,r. O < n →
  p_ord n (nth_prime i) = 〈O,r〉
  → (nth_prime i) ∤ n.
#n #i #r #posn #Hord
lapply (p_ord_to_exp1 … Hord) // * #H 
normalize <plus_n_O // 
qed.

theorem p_ord_to_not_eq_O : ∀n,p,q,r. 1<n →
  p_ord n (nth_prime p) = 〈q,r〉 → r≠O.
#n #p #q #r #lt1n #Hord
cut (O<n) [@lt_to_le //] #posn
lapply (p_ord_to_exp1 …posn … Hord)
  [@lt_SO_nth_prime_n 
  |* #H1 #H2 @(not_to_not …(lt_to_not_eq … posn))
   #eqr >eqr in H2; //
  ]
qed.

definition ord :nat → nat → nat ≝
  λn,p. fst ?? (p_ord n p).

definition ord_rem :nat → nat → nat ≝
  λn,p. snd ?? (p_ord n p).

lemma ord_eq: ∀n,p. ord n p = fst ?? (p_ord n p). //
qed.

lemma ord_rem_eq: ∀n,p. ord_rem n p = snd ?? (p_ord n p). //
qed.

theorem divides_to_ord: ∀p,n,m:nat. 
  O < n → O < m → prime p → divides n m 
  → divides (ord_rem n p) (ord_rem m p) ∧ (ord n p) ≤ (ord m p).  
#p #n #m #H #H1 #H2 #H3
@(divides_to_p_ord p ? ? ? ? n m H H1 H2 H3) 
  [@eq_pair_fst_snd|@eq_pair_fst_snd]
qed.

theorem divides_to_divides_ord_rem: ∀p,n,m:nat. 
O < n → O < m → prime p → divides n m →
  divides (ord_rem n p) (ord_rem m p).
#p #n #m #H #H1 #H2 #H3 cases (divides_to_ord p n m H H1 H2 H3) // 
qed.

theorem divides_to_le_ord: ∀p,n,m:nat. 
O < n → O < m → prime p → divides n m →
  ord n p ≤ ord m p.  
#p #n #m #H #H1 #H2 #H3 cases (divides_to_ord p n m H H1 H2 H3) //
qed.

theorem exp_ord: \forall p,n. 1 < p → O < n → 
  n = p \sup (ord n p) * (ord_rem n p).
#p #n #H #H1
cases (p_ord_to_exp1 p n (ord n p) (ord_rem n p) H H1 ?)
  [// |@eq_pair_fst_snd]
qed.

theorem divides_ord_rem: ∀p,n. 1 < p → O < n 
  → divides (ord_rem n p) n. 
#p #n #H #H1 %{(p \sup (ord n p))} >commutative_times @exp_ord // 
qed.

theorem lt_O_ord_rem: ∀p,n. 1 < p → O < n → O < ord_rem n p. 
#p #n #H #H1 
cases (le_to_or_lt_eq … (le_O_n (ord_rem n p))) //
#remO lapply(divides_ord_rem ?? H H1) <remO -remO #Hdiv0  
@False_ind @(absurd (0=n)) [cases Hdiv0 // | @lt_to_not_eq //]
qed.

(* properties of ord e ord_rem *)

theorem ord_times: ∀p,m,n.O<m → O<n → prime p →
  ord (m*n) p = ord m p+ord n p.
#p #m #n #H #H1 #H2 
lapply (p_ord_times ??? (ord m p) (ord_rem m p) (ord n p) (ord_rem n p) H2 H H1 
  (eq_pair_fst_snd …) (eq_pair_fst_snd …)) #H3
  @(eq_f … (fst …) … H3)
qed.

theorem ord_exp: ∀p,m. 1 < p → ord (exp p m) p = m.
#p #m #H >ord_eq >(p_ord_exp1 p (exp p m) m (S O)) //
  [@(not_to_not … (lt_to_not_le … H)) @divides_to_le //
  |@lt_to_le // 
  ]
qed.

theorem not_divides_to_ord_O: 
∀p,m. prime p → p ∤ m → ord m p = O.
#p #m #H #H1 >ord_eq >(p_ord_exp1 p m O m) // @prime_to_lt_O //
qed.

theorem ord_O_to_not_divides: ∀p,m. O < m → prime p → 
  ord m p = O → p ∤ m.
#p #m #H #H1 #H2 
lapply (p_ord_to_exp1 p m (ord m p) (ord_rem m p) … H … (eq_pair_fst_snd …))
  [@prime_to_lt_SO //
  |* #H3 >H2 >commutative_times <times_n_1 //  
  ]
qed.

theorem divides_to_not_ord_O: 
∀p,m. O < m → prime p → divides p m →
  ord m p ≠ O.
#p #m #H #H1 #H2 % #H3 @(absurd … H2) @(ord_O_to_not_divides ? ? H H1 H3)
qed.

theorem not_ord_O_to_divides: 
∀p,m. O < m → prime p → (ord m p ≠ O) → divides p m.
#p #m #H #H1 #H2  >(exp_ord p m) in ⊢ (??%);
  [@(transitive_divides ? (exp p (ord m p)))
    [lapply H2 cases (ord m p) 
      [* #H3 @False_ind @H3 // 
      |#a #_ normalize % // 
      ]
    |%{(ord_rem m p)} //
    ]
  |//
  |@prime_to_lt_SO //
  ]
qed.

theorem not_divides_ord_rem: ∀m,p.O< m → 1 < p →
  p ∤  (ord_rem m p).
#m #p #H #H1 
lapply (p_ord_to_exp1 p m (ord m p) (ord_rem m p) ?? (eq_pair_fst_snd …)) // *
#H2 #H3 @H2
qed.

theorem ord_ord_rem: ∀p,q,m. O < m → prime p → prime q →q < p → 
  ord (ord_rem m p) q = ord m q.
#p #q #m #H #H1 #H2 #H3 >(exp_ord p m) in ⊢ (???(?%?));
  [>(ord_times … H2)
    [>not_divides_to_ord_O in ⊢ (???(?%?)); //
     @(not_to_not … (lt_to_not_eq ? ? H3))
     @(divides_exp_to_eq ? ? ? H2 H1)
    |@lt_O_ord_rem // @prime_to_lt_SO //
    |@lt_O_exp @prime_to_lt_O //
    ]
  |//
  |@prime_to_lt_SO //
  ]
qed.

theorem lt_ord_rem: ∀n,m. prime n → O < m →
  divides n m → ord_rem m n < m.
#n #m #H #H1 #H2 
cases (le_to_or_lt_eq (ord_rem m n) m ?) 
  [//
  |#Hm @False_ind <Hm in H2; #Habs @(absurd ? Habs)
   @not_divides_ord_rem // @prime_to_lt_SO //
  |@divides_to_le //
   @divides_ord_rem // @prime_to_lt_SO //
  ]
qed.

(* p_ord_inv may be used to encode the pair ord and rem into 
   a single natural number. *)
 
definition p_ord_inv ≝ λp,m,x. 
  let 〈q,r〉 ≝ p_ord x p in r*m+q.
  
theorem  eq_p_ord_inv: ∀p,m,x.
  p_ord_inv p m x = (ord_rem x p)*m+(ord x p).
#p #m #x normalize cases(p_ord_aux x x p) // 
qed.

theorem div_p_ord_inv: 
∀p,m,x. ord x p < m → p_ord_inv p m x / m = ord_rem x p.
#p #m #x >eq_p_ord_inv @div_plus_times
qed.

theorem mod_p_ord_inv: 
∀p,m,x. ord x p < m → p_ord_inv p m x \mod m = ord x p.
#p #m #x >eq_p_ord_inv @mod_plus_times
qed.
