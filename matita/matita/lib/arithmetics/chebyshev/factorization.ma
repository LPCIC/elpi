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

include "arithmetics/log.ma".
include "arithmetics/sigma_pi.ma". 
include "arithmetics/ord.ma".

theorem eq_pi_p_primeb_divides_b: ∀n,m.
∏_{p<n | primeb p ∧ dividesb p m} (exp p (ord m p))
  = ∏_{p<n | primeb p} (exp p (ord m p)).
#n #m elim n // #n1 #Hind cases (true_or_false (primeb n1)) #Hprime
  [>bigop_Strue in ⊢ (???%); //
   cases (true_or_false (dividesb n1 m)) #Hdivides
    [>bigop_Strue [@eq_f @Hind| @true_to_andb_true //]
  |>bigop_Sfalse
    [>not_divides_to_ord_O
      [whd in ⊢ (???(?%?)); //
      |@dividesb_false_to_not_divides //
      |@primeb_true_to_prime // 
      ]
    |>Hprime >Hdivides % 
    ]
  ]
|>bigop_Sfalse [>bigop_Sfalse // |>Hprime %]
]
qed.

lemma lt_1_max_prime: ∀n. 1 <  n → 
  1 < max (S n) (λi:nat.primeb i∧dividesb i n).
#n #lt1n
@(lt_to_le_to_lt ? (smallest_factor n))
  [@lt_SO_smallest_factor //
  |@true_to_le_max
    [@le_S_S @le_smallest_factor_n
    |@true_to_andb_true
      [@prime_to_primeb_true @prime_smallest_factor_n //
      |@divides_to_dividesb_true
        [@lt_O_smallest_factor @lt_to_le //
        |@divides_smallest_factor_n @lt_to_le //
        ]
      ]
    ]
  ]
qed. 

theorem lt_max_to_pi_p_primeb: ∀q,m. O<m → max (S m) (λi.primeb i ∧ dividesb i m)<q →
  m = ∏_{p < q | primeb p ∧ dividesb p m} (exp p (ord m p)).
#q elim q
  [#m #posm #Hmax normalize @False_ind @(absurd … Hmax (not_le_Sn_O ?))
  |#n #Hind #m #posm #Hmax 
   cases (true_or_false (primeb n∧dividesb n m)) #Hcase
    [>bigop_Strue
      [>(exp_ord n m … posm) in ⊢ (??%?);
        [@eq_f >(Hind (ord_rem m n))
          [@same_bigop
            [#x #ltxn cases (true_or_false (primeb x)) #Hx >Hx
              [cases (true_or_false (dividesb x (ord_rem m n))) #Hx1 >Hx1
                [@sym_eq @divides_to_dividesb_true
                  [@prime_to_lt_O @primeb_true_to_prime //
                  |@(transitive_divides ? (ord_rem m n))
                    [@dividesb_true_to_divides //
                    |@(divides_ord_rem … posm) @(transitive_lt … ltxn) 
                     @prime_to_lt_SO @primeb_true_to_prime //
                    ]
                  ]
                |@sym_eq @not_divides_to_dividesb_false
                  [@prime_to_lt_O @primeb_true_to_prime //
                  |@(ord_O_to_not_divides … posm)
                    [@primeb_true_to_prime //
                    |<(ord_ord_rem n … posm … ltxn)
                      [@not_divides_to_ord_O
                        [@primeb_true_to_prime //
                        |@dividesb_false_to_not_divides //
                        ]
                      |@primeb_true_to_prime //
                      |@primeb_true_to_prime @(andb_true_l ?? Hcase)
                      ]
                    ]
                  ]
                ]
              |//
              ]
            |#x #ltxn #Hx @eq_f @ord_ord_rem //
              [@primeb_true_to_prime @(andb_true_l ? ? Hcase)
              |@primeb_true_to_prime @(andb_true_l ? ? Hx)
              ]
            ]
          |@not_eq_to_le_to_lt
            [elim (exists_max_forall_false (λi:nat.primeb i∧dividesb i (ord_rem m n)) (S(ord_rem m n)))
              [* #Hex #Hord_rem cases Hex #x * #H6 #H7 % #H 
               >H in Hord_rem; #Hn @(absurd ?? (not_divides_ord_rem m n posm ?))
                [@dividesb_true_to_divides @(andb_true_r ?? Hn)
                |@prime_to_lt_SO @primeb_true_to_prime @(andb_true_l ?? Hn)
                ]
              |* #Hall #Hmax >Hmax @lt_to_not_eq @prime_to_lt_O
               @primeb_true_to_prime @(andb_true_l ?? Hcase)
              ]
            |@(transitive_le ? (max (S m) (λi:nat.primeb i∧dividesb i (ord_rem m n))))
              [@le_to_le_max @le_S_S @(divides_to_le … posm) @(divides_ord_rem … posm)
               @prime_to_lt_SO @primeb_true_to_prime @(andb_true_l ?? Hcase)
              |@(transitive_le ? (max (S m) (λi:nat.primeb i∧dividesb i m)))
                [@le_max_f_max_g #i #ltim #Hi 
                 cases (true_or_false (primeb i)) #Hprimei >Hprimei
                  [@divides_to_dividesb_true
                    [@prime_to_lt_O @primeb_true_to_prime //
                    |@(transitive_divides ? (ord_rem m n))
                      [@dividesb_true_to_divides @(andb_true_r ?? Hi)
                      |@(divides_ord_rem … posm)
                       @prime_to_lt_SO @primeb_true_to_prime
                       @(andb_true_l ?? Hcase)
                      ]
                    ]
                  |>Hprimei in Hi; #Hi @Hi 
                  ]
                |@le_S_S_to_le //
                ]
              ]
            ]
          |@(lt_O_ord_rem … posm) @prime_to_lt_SO
           @primeb_true_to_prime @(andb_true_l ?? Hcase)
          ]
        |@prime_to_lt_SO @primeb_true_to_prime @(andb_true_l ?? Hcase)
        ]
      |//
      ]
    |cases (le_to_or_lt_eq ?? posm) #Hm
      [>bigop_Sfalse
        [@(Hind … posm) @false_to_lt_max
          [@(lt_to_le_to_lt ? (max (S m) (λi:nat.primeb i∧dividesb i m)))
            [@lt_to_le @lt_1_max_prime // 
            |@le_S_S_to_le //
            ]
          |//
          |@le_S_S_to_le //
          ]
        |@Hcase
        ]
      |<Hm 
       <(bigop_false (S n) ? 1 times (λp:nat.p\sup(ord 1 p))) in ⊢ (??%?);
       @same_bigop
        [#i #lein cases (true_or_false (primeb i)) #primei >primei //
         @sym_eq @not_divides_to_dividesb_false
          [@prime_to_lt_O @primeb_true_to_prime //
          |% #divi @(absurd ?? (le_to_not_lt i 1 ?))
            [@prime_to_lt_SO @(primeb_true_to_prime ? primei)
            |@divides_to_le // 
            ]
          ]
        |// 
        ]
      ]
    ]
  ]
qed.

(* factorization of n into primes *)
theorem pi_p_primeb_dividesb: ∀n. O < n → 
  n = ∏_{ p < S n | primeb p ∧ dividesb p n} (exp p (ord n p)).
#n #posn @lt_max_to_pi_p_primeb // @lt_max_n @le_S @posn
qed.

theorem pi_p_primeb: ∀n. O < n → 
  n = ∏_{ p < (S n) | primeb p}(exp p (ord n p)).
#n #posn <eq_pi_p_primeb_divides_b @pi_p_primeb_dividesb //
qed.

(* more result on order functions *)
theorem le_ord_log: ∀n,p. O < n → 1 < p →
  ord n p ≤ log p n.
#n #p #posn #lt1p >(exp_ord p ? lt1p posn) in ⊢ (??(??%)); 
>log_exp // @lt_O_ord_rem //
qed.

theorem sigma_p_dividesb:
∀m,n,p. O < n → prime p → p ∤ n →
m = ∑_{ i < m | dividesb (p\sup (S i)) ((exp p m)*n)} 1.
#m elim m // -m #m #Hind #n #p #posn #primep #ndivp
>bigop_Strue
  [>commutative_plus <plus_n_Sm @eq_f <plus_n_O
   >(Hind n p posn primep ndivp) in ⊢ (? ? % ?); 
   @same_bigop
    [#i #ltim cases (true_or_false (dividesb (p\sup(S i)) (p\sup m*n))) #Hc >Hc
      [@sym_eq @divides_to_dividesb_true
        [@lt_O_exp @prime_to_lt_O //
        |%{((exp p (m - i))*n)} <associative_times
         <exp_plus_times @eq_f2 // @eq_f normalize @eq_f >commutative_plus 
         @plus_minus_m_m @lt_to_le //
        ]
      |@False_ind @(absurd ?? (dividesb_false_to_not_divides ? ? Hc))
       %{((exp p (m - S i))*n)} <associative_times <exp_plus_times @eq_f2
        [@eq_f >commutative_plus @plus_minus_m_m //
           assumption
        |%
        ]
      ]
    |// 
    ]
  |@divides_to_dividesb_true
    [@lt_O_exp @prime_to_lt_O // | %{n} //]
  ]
qed.
  
theorem sigma_p_dividesb1:
∀m,n,p,k. O < n → prime p → p ∤ n → m ≤ k →
  m = ∑_{i < k | dividesb (p\sup (S i)) ((exp p m)*n)} 1.
#m #n #p #k #posn #primep #ndivp #lemk
lapply (prime_to_lt_SO ? primep) #lt1p
lapply (prime_to_lt_O ? primep) #posp
>(sigma_p_dividesb m n p posn primep ndivp) in ⊢ (??%?);
>(pad_bigop k m) // @same_bigop
  [#i #ltik cases (true_or_false (leb m i)) #Him > Him
    [whd in ⊢(??%?); @sym_eq 
     @not_divides_to_dividesb_false
      [@lt_O_exp //
      |lapply (leb_true_to_le … Him) -Him #Him
       % #Hdiv @(absurd ?? (le_to_not_lt ?? Him))
       (* <(ord_exp p m lt1p) *) >(plus_n_O m)
       <(not_divides_to_ord_O ?? primep ndivp)
       <(ord_exp p m lt1p)
       <ord_times //
        [whd <(ord_exp p (S i) lt1p)
         @divides_to_le_ord //
          [@lt_O_exp // 
          |>(times_n_O O) @lt_times // @lt_O_exp //
          ]
        |@lt_O_exp //
        ]
      ]
    |%
    ]
  |//
  ]
qed.

theorem eq_ord_sigma_p:
∀n,m,x. O < n → prime x → 
exp x m ≤ n → n < exp x (S m) →
ord n x= ∑_{i < m | dividesb (x\sup (S i)) n} 1.
#n #m #x #posn #primex #Hexp #ltn
lapply (prime_to_lt_SO ? primex) #lt1x 
>(exp_ord x n) in ⊢ (???%); // @sigma_p_dividesb1 
  [@lt_O_ord_rem // 
  |//
  |@not_divides_ord_rem // 
  |@le_S_S_to_le @(le_to_lt_to_lt ? (log x n))
    [@le_ord_log // 
    |@(lt_exp_to_lt x)
      [@lt_to_le //
      |@(le_to_lt_to_lt ? n ? ? ltn) @le_exp_log //
      ]
    ]
  ]
qed.
    
theorem pi_p_primeb1: ∀n. O < n → 
n = ∏_{p < S n| primeb p} 
  (∏_{i < log p n| dividesb (exp p (S i)) n} p).
#n #posn >(pi_p_primeb n posn) in ⊢ (??%?);
@same_bigop
  [// 
  |#p #ltp #primep >exp_sigma @eq_f @eq_ord_sigma_p 
    [//
    |@primeb_true_to_prime //
    |@le_exp_log // 
    |@lt_exp_log @prime_to_lt_SO @primeb_true_to_prime //
    ]
  ]
qed.

(* the factorial function *)
theorem eq_fact_pi_p:∀n.
  fact n = ∏_{i < S n | leb 1 i} i.
#n elim n // #n1 #Hind whd in ⊢ (??%?); >commutative_times >bigop_Strue 
  [@eq_f // | % ]
qed.
   
theorem eq_sigma_p_div: ∀n,q.O < q →
  ∑_{ m < S n | leb (S O) m ∧ dividesb q m} 1 =n/q.
#n #q #posq
@(div_mod_spec_to_eq n q ? (n \mod q) ? (n \mod q))
  [@div_mod_spec_intro
    [@lt_mod_m_m // 
    |elim n
      [normalize cases q // 
      |#n1 #Hind cases (or_div_mod1 n1 q posq)
        [* #divq #eqn1  >divides_to_mod_O //
         <plus_n_O >bigop_Strue
          [>eqn1 in ⊢ (??%?); @eq_f2
            [<commutative_plus <plus_n_Sm <plus_n_O @eq_f
             @(div_mod_spec_to_eq n1 q (div n1 q) (mod n1 q) ? (mod n1 q))
              [@div_mod_spec_div_mod //
              |@div_mod_spec_intro [@lt_mod_m_m // | //]
              ]
            |%
            ]
          |@true_to_andb_true [//|@divides_to_dividesb_true //]
          ]
        |* #ndiv #eqn1 >bigop_Sfalse
          [>(mod_S … posq) 
            [< plus_n_Sm @eq_f //
            |cases (le_to_or_lt_eq (S (mod n1 q)) q ?)
              [//
              |#eqq @False_ind cases ndiv #Hdiv @Hdiv
               %{(S(div n1 q))} <times_n_Sm <commutative_plus //
              |@lt_mod_m_m //
              ]
            ]
          |>not_divides_to_dividesb_false //
          ]
        ]
      ]
    ]
  |@div_mod_spec_div_mod //
  ]
qed.       

lemma timesACdef: ∀n,m. timesAC n m = n * m.
// qed-.

(* still another characterization of the factorial *)
theorem fact_pi_p: ∀n. 
fact n = ∏_{ p < S n | primeb p} 
           (∏_{i < log p n} (exp p (n /(exp p (S i))))).
#n >eq_fact_pi_p
@(trans_eq ?? 
  (∏_{m < S n | leb 1 m}
   (∏_{p < S m | primeb p}
    (∏_{i < log p m | dividesb (exp p (S i)) m} p))))
  [@same_bigop [// |#x #Hx1 #Hx2  @pi_p_primeb1 @leb_true_to_le //]
  |@(trans_eq ?? 
    (∏_{m < S n | leb 1 m}
      (∏_{p < S m | primeb p ∧ leb p m}
       (∏_{ i < log p m | dividesb ((p)\sup(S i)) m} p))))
    [@same_bigop
      [//
      |#x #Hx1 #Hx2 @same_bigop
        [#p #ltp >(le_to_leb_true … (le_S_S_to_le …ltp))
         cases (primeb p) //
        |//
        ]
      ]
    |@(trans_eq ?? 
      (∏_{m < S n | leb 1 m}
       (∏_{p < S n | primeb p ∧ leb p m}
         (∏_{i < log p m |dividesb ((p)\sup(S i)) m} p))))
      [@same_bigop
        [//
        |#p #Hp1 #Hp2 @pad_bigop1 
          [@Hp1
          |#i #lti #upi >lt_to_leb_false
            [cases (primeb i) //|@lti]
          ] 
        ]
      |(* make a general theorem *)
       @(trans_eq ?? 
        (∏_{p < S n | primeb p}
          (∏_{m < S n | leb p m}
           (∏_{i < log p m | dividesb (p^(S i)) m} p))))
        [@(bigop_commute … timesAC … (lt_O_S n) (lt_O_S n))
         #i #j #lti #ltj
         cases (true_or_false (primeb j ∧ leb j i)) #Hc >Hc
          [>(le_to_leb_true 1 i)
            [//
            |@(transitive_le ? j)
              [@prime_to_lt_O @primeb_true_to_prime @(andb_true_l ? ? Hc)
              |@leb_true_to_le @(andb_true_r ?? Hc)
              ]
            ]
          |cases(leb 1 i) // 
          ]
        |@same_bigop
          [//
          |#p #Hp1 #Hp2
           @(trans_eq ?? 
            (∏_{m < S n | leb p m}
             (∏_{i < log p n | dividesb (p\sup(S i)) m} p)))
            [@same_bigop
              [//
              |#x #Hx1 #Hx2 @sym_eq 
               @sym_eq @pad_bigop1
                [@le_log
                  [@prime_to_lt_SO @primeb_true_to_prime //
                  |@le_S_S_to_le //
                  ]
                |#i #Hi1 #Hi2 @not_divides_to_dividesb_false
                  [@lt_O_exp @prime_to_lt_O @primeb_true_to_prime //
                  |@(not_to_not … (lt_to_not_le x (exp p (S i)) ?)) 
                    [#H @divides_to_le // @(lt_to_le_to_lt ? p)
                      [@prime_to_lt_O @primeb_true_to_prime //
                      |@leb_true_to_le //
                      ]
                    |@(lt_to_le_to_lt ? (exp p (S(log p x))))
                      [@lt_exp_log @prime_to_lt_SO @primeb_true_to_prime //
                      |@le_exp
                        [@ prime_to_lt_O @primeb_true_to_prime //
                        |@le_S_S //
                        ]
                      ]
                    ]
                  ]
                ]
              ]
            |@
             (trans_eq ? ? 
              (∏_{i < log p n}
                (∏_{m < S n | leb p m ∧ dividesb (p\sup(S i)) m} p)))
              [@(bigop_commute ?????? nat 1 timesAC (λm,i.p) ???) //
               cut (p ≤ n) [@le_S_S_to_le //] #lepn 
               @(lt_O_log … lepn) @(lt_to_le_to_lt … lepn) @prime_to_lt_SO 
               @primeb_true_to_prime //
              |@same_bigop
                [//
                |#m #ltm #_ >exp_sigma @eq_f
                 @(trans_eq ?? 
                  (∑_{i < S n |leb 1 i∧dividesb (p\sup(S m)) i} 1))
                  [@same_bigop
                    [#i #lti
                     cases (true_or_false (dividesb (p\sup(S m)) i)) #Hc >Hc 
                      [cases (true_or_false (leb p i)) #Hp3 >Hp3 
                        [>le_to_leb_true 
                          [//
                          |@(transitive_le ? p)
                            [@prime_to_lt_O @primeb_true_to_prime //
                            |@leb_true_to_le //
                            ]
                          ]
                        |>lt_to_leb_false
                          [//
                          |@not_le_to_lt
                           @(not_to_not ??? (leb_false_to_not_le ?? Hp3)) #posi
                           @(transitive_le ? (exp p (S m)))
                            [>(exp_n_1 p) in ⊢ (?%?);
                             @le_exp
                              [@prime_to_lt_O @primeb_true_to_prime //
                              |@le_S_S @le_O_n
                              ]
                            |@(divides_to_le … posi)
                             @dividesb_true_to_divides //
                            ]
                          ]
                        ]
                      |cases (leb p i) cases (leb 1 i) //
                      ]
                    |// 
                    ]
                  |@eq_sigma_p_div @lt_O_exp
                   @prime_to_lt_O @primeb_true_to_prime //
                  ]
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
qed.

theorem fact_pi_p2: ∀n. fact (2*n) =
∏_{p < S (2*n) | primeb p} 
  (∏_{i < log p (2*n)}
    (exp p (2*(n /(exp p (S i))))*(exp p (mod (2*n /(exp p (S i))) 2)))).
#n >fact_pi_p @same_bigop
  [//
  |#p #ltp #primep @same_bigop
    [//
    |#i #lti #_ <exp_plus_times @eq_f
     >commutative_times in ⊢ (???(?%?));
     cut (0 < p ^ (S i)) 
       [@lt_O_exp @prime_to_lt_O @primeb_true_to_prime //]
     generalize in match (p ^(S i)); #a #posa
     >(div_times_times n a 2) // >(commutative_times n 2)
     <eq_div_div_div_times //
    ]
  ]
qed.

theorem fact_pi_p3: ∀n. fact (2*n) =
∏_{p < S (2*n) | primeb p}
  (∏_{i < log p (2*n)}(exp p (2*(n /(exp p (S i)))))) *
∏_{p < S (2*n) | primeb p}
  (∏_{i < log p (2*n)}(exp p (mod (2*n /(exp p (S i))) 2))).
#n <times_pi >fact_pi_p2 @same_bigop
  [// 
  |#p #ltp #primep @times_pi
  ]
qed.

theorem pi_p_primeb4: ∀n. 1 < n →
∏_{p < S (2*n) | primeb p} 
  (∏_{i < log p (2*n)}(exp p (2*(n /(exp p (S i))))))
= 
∏_{p < S n | primeb p}
  (∏_{i < log p (2*n)}(exp p (2*(n /(exp p (S i)))))).
#n #lt1n
@sym_eq @(pad_bigop_nil … timesAC)
  [@le_S_S /2 by /
  |#i #ltn #lti %2
   >log_i_2n //
    [>bigop_Strue // whd in ⊢ (??(??%)?); <times_n_1
     <exp_n_1 >eq_div_O //
    |@le_S_S_to_le // 
    ]
  ]
qed.
   
theorem pi_p_primeb5: ∀n. 1 < n →
∏_{p < S (2*n) | primeb p}
  (∏_{i < log p (2*n)} (exp p (2*(n /(exp p (S i))))))
= 
∏_{p < S n | primeb p} 
  (∏_{i < log p n} (exp p (2*(n /(exp p (S i)))))).
#n #lt1n >(pi_p_primeb4 ? lt1n) @same_bigop
  [//
  |#p #lepn #primebp @sym_eq @(pad_bigop_nil … timesAC) 
    [@le_log
      [@prime_to_lt_SO @primeb_true_to_prime //
      |// 
      ]
    |#i #lelog #lti %2 >eq_div_O //
     @(lt_to_le_to_lt ? (exp p (S(log p n))))
      [@lt_exp_log @prime_to_lt_SO @primeb_true_to_prime //
      |@le_exp
        [@prime_to_lt_O @primeb_true_to_prime // |@le_S_S //]      
      ]
    ]
  ]
qed.

theorem exp_fact_2: ∀n.
exp (fact n) 2 = 
  ∏_{p < S n| primeb p}
    (∏_{i < log p n} (exp p (2*(n /(exp p (S i)))))).
#n >fact_pi_p <exp_pi @same_bigop
  [//
  |#p #ltp #primebp @sym_eq 
   @(trans_eq ?? (∏_{x < log p n} (exp (exp p (n/(exp p (S x)))) 2)))
  [@same_bigop
    [//
    |#x #ltx #_ @sym_eq >commutative_times @exp_exp_times
    ]
  |@exp_pi
  ]
qed.

definition B ≝ λn.
∏_{p < S n | primeb p} 
  (∏_{i < log p n} (exp p (mod (n /(exp p (S i))) 2))).
  
lemma Bdef : ∀n.B n = 
  ∏_{p < S n | primeb p} 
  (∏_{i < log p n} (exp p (mod (n /(exp p (S i))) 2))).
// qed-.

example B_SSSO: B 3 = 6. //
qed.

example B_SSSSO: B 4 = 6. //
qed.

example B_SSSSSO: B 5 = 30. //
qed.

example B_SSSSSSO: B 6 = 20. //
qed.

example B_SSSSSSSO: B 7 = 140. //
qed.

example B_SSSSSSSSO: B 8 = 70. //
qed.

theorem eq_fact_B:∀n. 1 < n →
  (2*n)! = exp (n!) 2 * B(2*n).
#n #lt1n >fact_pi_p3 @eq_f2
  [@sym_eq >pi_p_primeb5 [@exp_fact_2|//] |// ]
qed.

theorem lt_SO_to_le_B_exp: ∀n. 1 < n →
  B (2*n) ≤ exp 2 (pred (2*n)).
#n #lt1n @(le_times_to_le (exp (fact n) 2))
  [@lt_O_exp //
  |<(eq_fact_B … lt1n) <commutative_times in ⊢ (??%);
   >exp_2 <associative_times @fact_to_exp 
  ]
qed.

theorem le_B_exp: ∀n.
  B (2*n) ≤ exp 2 (pred (2*n)).
#n cases n
  [@le_n|#n1 cases n1 [@le_n |#n2 @lt_SO_to_le_B_exp @le_S_S @lt_O_S]]
qed.

theorem lt_4_to_le_B_exp: ∀n.4 < n →
  B (2*n) \le exp 2 ((2*n)-2).
#n #lt4n @(le_times_to_le (exp (fact n) 2))
  [@lt_O_exp //
  |<eq_fact_B
    [<commutative_times in ⊢ (??%); >exp_2 <associative_times
     @lt_4_to_fact //
    |@lt_to_le @lt_to_le @lt_to_le //
    ]
  ]
qed.

theorem lt_1_to_le_exp_B: ∀n. 1 < n →
  exp 2 (2*n) ≤ 2 * n * B (2*n).
#n #lt1n 
@(le_times_to_le (exp (fact n) 2))
  [@lt_O_exp @le_1_fact
  |<associative_times in ⊢ (??%); >commutative_times in ⊢ (??(?%?));
   >associative_times in ⊢ (??%); <(eq_fact_B … lt1n)
   <commutative_times; @exp_to_fact2 @lt_to_le // 
  ]
qed.

theorem le_exp_B: ∀n. O < n →
  exp 2 (2*n) ≤ 2 * n * B (2*n).
#n #posn cases posn
  [@le_n |#m #lt1m @lt_1_to_le_exp_B @le_S_S // ]
qed.