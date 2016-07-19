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

include "basics/types.ma".
include "arithmetics/div_and_mod.ma".

definition sameF_upto: nat → ∀A.relation(nat→A)  ≝
λk.λA.λf,g.∀i. i < k → f i = g i.
     
definition sameF_p: nat → (nat → bool) →∀A.relation(nat→A)  ≝
λk,p,A,f,g.∀i. i < k → p i = true → f i = g i.

lemma sameF_upto_le: ∀A,f,g,n,m. 
 n ≤m → sameF_upto m A f g → sameF_upto n A f g.
#A #f #g #n #m #lenm #samef #i #ltin @samef /2 by lt_to_le_to_lt/
qed.

lemma sameF_p_le: ∀A,p,f,g,n,m. 
 n ≤m → sameF_p m p A f g → sameF_p n p A f g.
#A #p #f #g #n #m #lenm #samef #i #ltin #pi @samef /2 by lt_to_le_to_lt/
qed.

(*
definition sumF ≝ λA.λf,g:nat → A.λn,i.
if_then_else ? (leb n i) (g (i-n)) (f i). 

lemma sumF_unfold: ∀A,f,g,n,i. 
sumF A f g n i = if_then_else ? (leb n i) (g (i-n)) (f i). 
// qed. *)

definition prodF ≝
 λA,B.λf:nat→A.λg:nat→B.λm,x.〈 f(div x m), g(mod x m) 〉.

(* bigop *)
let rec bigop (n:nat) (p:nat → bool) (B:Type[0])
   (nil: B) (op: B → B → B)  (f: nat → B) ≝
  match n with
   [ O ⇒ nil
   | S k ⇒ 
      match p k with
      [true ⇒ op (f k) (bigop k p B nil op f)
      |false ⇒ bigop k p B nil op f]
   ].
   
notation "\big  [ op , nil ]_{ ident i < n | p } f"
  with precedence 80
for @{'bigop $n $op $nil (λ${ident i}. $p) (λ${ident i}. $f)}.

notation "\big [ op , nil ]_{ ident i < n } f"
  with precedence 80
for @{'bigop $n $op $nil (λ${ident i}.true) (λ${ident i}. $f)}.

interpretation "bigop" 'bigop n op nil p f = (bigop n p ? nil op f).

notation "\big  [ op , nil ]_{ ident j ∈ [a,b[ | p } f"
  with precedence 80
for @{'bigop ($b-$a) $op $nil (λ${ident j}.((λ${ident j}.$p) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
  
notation "\big  [ op , nil ]_{ ident j ∈ [a,b[ } f"
  with precedence 80
for @{'bigop ($b-$a) $op $nil (λ${ident j}.((λ${ident j}.true) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.  
 
(* notation "\big  [ op , nil ]_{( term 55) a ≤ ident j < b | p } f"
  with precedence 80
for @{\big[$op,$nil]_{${ident j} < ($b-$a) | ((λ${ident j}.$p) (${ident j}+$a))}((λ${ident j}.$f)(${ident j}+$a))}.
*)
 
interpretation "bigop" 'bigop n op nil p f = (bigop n p ? nil op f).
   
lemma bigop_Strue: ∀k,p,B,nil,op.∀f:nat→B. p k = true →
  \big[op,nil]_{i < S k | p i}(f i) =
    op (f k) (\big[op,nil]_{i < k | p i}(f i)).
#k #p #B #nil #op #f #H normalize >H // qed.

lemma bigop_Sfalse: ∀k,p,B,nil,op.∀f:nat→B. p k = false →
  \big[op,nil]_{ i < S k | p i}(f i) =
    \big[op,nil]_{i < k | p i}(f i).
#k #p #B #nil #op #f #H normalize >H // qed. 
 
lemma same_bigop : ∀k,p1,p2,B,nil,op.∀f,g:nat→B. 
  sameF_upto k bool p1 p2 → sameF_p k p1 B f g →
  \big[op,nil]_{i < k | p1 i}(f i) = 
    \big[op,nil]_{i < k | p2 i}(g i).
#k #p1 #p2 #B #nil #op #f #g (elim k) // 
#n #Hind #samep #samef normalize >Hind /2/
<(samep … (le_n …)) cases(true_or_false (p1 n)) #H1 >H1 
normalize // <(samef … (le_n …) H1) // 
qed.

theorem pad_bigop: ∀k,n,p,B,nil,op.∀f:nat→B. n ≤ k → 
\big[op,nil]_{i < n | p i}(f i)
  = \big[op,nil]_{i < k | if leb n i then false else p i}(f i).
#k #n #p #B #nil #op #f #lenk (elim lenk) 
  [@same_bigop #i #lti // >(not_le_to_leb_false …) /2/
  |#j #leup #Hind >bigop_Sfalse >(le_to_leb_true … leup) // 
  ] qed.
  
theorem pad_bigop1: ∀k,n,p,B,nil,op.∀f:nat→B. n ≤ k → 
  (∀i. n ≤ i → i < k → p i = false) →
  \big[op,nil]_{i < n | p i}(f i) 
    = \big[op,nil]_{i < k | p i}(f i).
#k #n #p #B #nil #op #f #lenk (elim lenk) 
  [#_ @same_bigop #i #lti // 
  |#j #leup #Hind #Hfalse >bigop_Sfalse 
    [@Hind #i #leni #ltij @Hfalse // @le_S //  
    |@Hfalse // 
    ] 
  ] 
qed.
  
theorem bigop_false: ∀n,B,nil,op.∀f:nat→B.
  \big[op,nil]_{i < n | false }(f i) = nil.  
#n #B #nil #op #f elim n // #n1 #Hind 
>bigop_Sfalse // 
qed.

record Aop (A:Type[0]) (nil:A) : Type[0] ≝
  {op :2> A → A → A; 
   nill:∀a. op nil a = a; 
   nilr:∀a. op a nil = a;
   assoc: ∀a,b,c.op a (op b c) = op (op a b) c
  }.
  
theorem pad_bigop_nil: ∀k,n,p,B,nil.∀op:Aop B nil.∀f:nat→B. n ≤ k → 
  (∀i. n ≤ i → i < k → p i = false ∨ f i = nil) →
  \big[op,nil]_{i < n | p i}(f i) 
    = \big[op,nil]_{i < k | p i}(f i).
#k #n #p #B #nil #op #f #lenk (elim lenk) 
  [#_ @same_bigop #i #lti // 
  |#j #leup #Hind #Hfalse cases (true_or_false (p j)) #Hpj
    [>bigop_Strue // 
     cut (f j = nil) 
      [cases (Hfalse j leup (le_n … )) // >Hpj #H destruct (H)] #Hfj
     >Hfj >nill @Hind #i #leni #ltij
     cases (Hfalse i leni (le_S … ltij)) /2/
    |>bigop_Sfalse // @Hind #i #leni #ltij
     cases (Hfalse i leni (le_S … ltij)) /2/
    ]  
  ]
qed.

theorem bigop_sum: ∀k1,k2,p1,p2,B.∀nil.∀op:Aop B nil.∀f,g:nat→B.
op (\big[op,nil]_{i<k1|p1 i}(f i)) \big[op,nil]_{i<k2|p2 i}(g i) =
      \big[op,nil]_{i<k1+k2|if leb k2 i then p1 (i-k2) else p2 i}
        (if leb k2 i then f (i-k2) else g i).
#k1 #k2 #p1 #p2 #B #nil #op #f #g (elim k1)
  [normalize >nill @same_bigop #i #lti 
   >(lt_to_leb_false … lti) normalize /2/
  |#i #Hind normalize <minus_plus_m_m (cases (p1 i)) 
   >(le_to_leb_true … (le_plus_n …)) normalize <Hind //
   <assoc //
  ]
qed.

lemma plus_minus1: ∀a,b,c. c ≤ b → a + (b -c) = a + b -c.
#a #b #c #lecb @sym_eq @plus_to_minus >(commutative_plus c) 
>associative_plus <plus_minus_m_m //
qed.

theorem bigop_I: ∀n,p,B.∀nil.∀op:Aop B nil.∀f:nat→B.
\big[op,nil]_{i∈[0,n[ |p i}(f i) = \big[op,nil]_{i < n|p i}(f i). 
#n #p #B #nil #op #f <minus_n_O @same_bigop //
qed.
     
theorem bigop_I_gen: ∀a,b,p,B.∀nil.∀op:Aop B nil.∀f:nat→B. a ≤b →
\big[op,nil]_{i∈[a,b[ |p i}(f i) = \big[op,nil]_{i < b|leb a i ∧ p i}(f i). 
#a #b elim b // -b #b #Hind #p #B #nil #op #f #lea
cut (∀a,b. a ≤ b → S b - a = S (b -a)) 
  [#a #b cases a // #a1 #lta1 normalize >eq_minus_S_pred >S_pred 
   /2 by lt_plus_to_minus_r/] #Hcut
cases (le_to_or_lt_eq … lea) #Ha
  [cases (true_or_false (p b)) #Hcase
    [>bigop_Strue [2: >Hcase >(le_to_leb_true a b) // @le_S_S_to_le @Ha]
     >(Hcut … (le_S_S_to_le … Ha))
     >bigop_Strue 
      [@eq_f2 
        [@eq_f <plus_minus_m_m [//|@le_S_S_to_le //] @Hind 
        |@Hind @le_S_S_to_le //
        ]
      |<plus_minus_m_m // @le_S_S_to_le //
      ]
   |>bigop_Sfalse [2: >Hcase cases (leb a b)//]
     >(Hcut … (le_S_S_to_le … Ha)) >bigop_Sfalse
      [@Hind @le_S_S_to_le // | <plus_minus_m_m // @le_S_S_to_le //]
    ]
  |<Ha <minus_n_n whd in ⊢ (??%?); <(bigop_false a B nil op f) in ⊢ (??%?);
   @same_bigop // #i #ltia >(not_le_to_leb_false a i) // @lt_to_not_le //
  ]
qed.    
     
theorem bigop_sumI: ∀a,b,c,p,B.∀nil.∀op:Aop B nil.∀f:nat→B.
a ≤ b → b ≤ c →
\big[op,nil]_{i∈[a,c[ |p i}(f i) = 
  op (\big[op,nil]_{i ∈ [b,c[ |p i}(f i)) 
      \big[op,nil]_{i ∈ [a,b[ |p i}(f i).
#a #b # c #p #B #nil #op #f #leab #lebc 
>(plus_minus_m_m (c-a) (b-a)) in ⊢ (??%?); /2/
>minus_plus >(commutative_plus a) <plus_minus_m_m //
>bigop_sum (cut (∀i. b -a ≤ i → i+a = i-(b-a)+b))
  [#i #lei >plus_minus // <plus_minus1 
     [@eq_f @sym_eq @plus_to_minus /2/ | /2/]] 
#H @same_bigop #i #ltic @leb_elim normalize // #lei <H //
qed.   

theorem bigop_a: ∀a,b,B.∀nil.∀op:Aop B nil.∀f:nat→B. a ≤ b →
\big[op,nil]_{i∈[a,S b[ }(f i) = 
  op (\big[op,nil]_{i ∈ [a,b[ }(f (S i))) (f a).
#a #b #B #nil #op #f #leab 
>(bigop_sumI a (S a) (S b)) [|@le_S_S //|//] @eq_f2 
  [@same_bigop // |<minus_Sn_n normalize @nilr]
qed.
  
theorem bigop_0: ∀n,B.∀nil.∀op:Aop B nil.∀f:nat→B.
\big[op,nil]_{i < S n}(f i) = 
  op (\big[op,nil]_{i < n}(f (S i))) (f 0).
#n #B #nil #op #f 
<bigop_I >bigop_a [|//] @eq_f2 [|//] <minus_n_O 
@same_bigop //
qed.    

theorem bigop_prod: ∀k1,k2,p1,p2,B.∀nil.∀op:Aop B nil.∀f: nat →nat → B.
\big[op,nil]_{x<k1|p1 x}(\big[op,nil]_{i<k2|p2 x i}(f x i)) =
  \big[op,nil]_{i<k1*k2|andb (p1 (i/k2)) (p2 (i/k2) (i \mod k2))}
     (f (i/k2) (i \mod k2)).
#k1 #k2 #p1 #p2 #B #nil #op #f (elim k1) //
#n #Hind cases(true_or_false (p1 n)) #Hp1
  [>bigop_Strue // >Hind >bigop_sum @same_bigop
   #i #lti @leb_elim // #lei cut (i = n*k2+(i-n*k2)) /2 by plus_minus/
   #eqi [|#H] >eqi in ⊢ (???%);
     >div_plus_times /2 by monotonic_lt_minus_l/ 
     >Hp1 >(mod_plus_times …) /2 by refl, monotonic_lt_minus_l, eq_f/
  |>bigop_Sfalse // >Hind >(pad_bigop (S n*k2)) // @same_bigop
   #i #lti @leb_elim // #lei cut (i = n*k2+(i-n*k2)) /2 by plus_minus/
   #eqi >eqi in ⊢ (???%); >div_plus_times 
   /2 by refl, monotonic_lt_minus_l, trans_eq/ 
  ]
qed.

record ACop (A:Type[0]) (nil:A) : Type[0] ≝
  {aop :> Aop A nil; 
   comm: ∀a,b.aop a b = aop b a
  }.
 
lemma bigop_op: ∀k,p,B.∀nil.∀op:ACop B nil.∀f,g: nat → B.
op (\big[op,nil]_{i<k|p i}(f i)) (\big[op,nil]_{i<k|p i}(g i)) =
  \big[op,nil]_{i<k|p i}(op (f i) (g i)).
#k #p #B #nil #op #f #g (elim k) [normalize @nill]
-k #k #Hind (cases (true_or_false (p k))) #H
  [>bigop_Strue // >bigop_Strue // >bigop_Strue //
   normalize <assoc <assoc in ⊢ (???%); @eq_f >assoc >comm in ⊢ (??(????%?)?);
   <assoc @eq_f @Hind
  |>bigop_Sfalse // >bigop_Sfalse // >bigop_Sfalse //
  ]
qed.

lemma bigop_diff: ∀p,B.∀nil.∀op:ACop B nil.∀f:nat → B.∀i,n.
  i < n → p i = true →
  \big[op,nil]_{x<n|p x}(f x)=
    op (f i) (\big[op,nil]_{x<n|andb(notb(eqb i x))(p x)}(f x)).
#p #B #nil #op #f #i #n (elim n) 
  [#ltO @False_ind /2/
  |#n #Hind #lein #pi cases (le_to_or_lt_eq … (le_S_S_to_le …lein)) #Hi
    [cut (andb(notb(eqb i n))(p n) = (p n))
      [>(not_eq_to_eqb_false … (lt_to_not_eq … Hi)) //] #Hcut
     cases (true_or_false (p n)) #pn 
      [>bigop_Strue // >bigop_Strue //
       normalize >assoc >(comm ?? op (f i) (f n)) <assoc >Hind //
      |>bigop_Sfalse // >bigop_Sfalse // >Hind //  
      ]
    |<Hi >bigop_Strue // @eq_f >bigop_Sfalse  
       [@same_bigop // #k #ltki >not_eq_to_eqb_false /2/
       |>eq_to_eqb_true // 
       ]
     ]
   ]
qed.

(* range *)
record range (A:Type[0]): Type[0] ≝
  {enum:nat→A; upto:nat; filter:nat→bool}.
  
definition sub_hk: (nat→nat)→(nat→nat)→∀A:Type[0].relation (range A) ≝
λh,k,A,I,J.∀i.i<(upto A I) → (filter A I i)=true → 
  (h i < upto A J
  ∧ filter A J (h i) = true
  ∧ k (h i) = i).

definition iso: ∀A:Type[0].relation (range A) ≝
  λA,I,J.∃h,k. 
    (∀i. i < (upto A I) → (filter A I i) = true → 
       enum A I i = enum A J (h i)) ∧
    sub_hk h k A I J ∧ sub_hk k h A J I.
  
lemma sub_hkO: ∀h,k,A,I,J. upto A I = 0 → sub_hk h k A I J.
#h #k #A #I #J #up0 #i #lti >up0 @False_ind /2/
qed.

lemma sub0_to_false: ∀h,k,A,I,J. upto A I = 0 → sub_hk h k A J I → 
  ∀i. i < upto A J → filter A J i = false.
#h #k #A #I #J #up0 #sub #i #lti cases(true_or_false (filter A J i)) //
#ptrue (cases (sub i lti ptrue)) * #hi @False_ind /2/ 
qed.

lemma sub_lt: ∀A,e,p,n,m. n ≤ m → 
  sub_hk (λx.x) (λx.x) A (mk_range A e n p) (mk_range A e m p).
#A #e #f #n #m #lenm #i #lti #fi % // % /2 by lt_to_le_to_lt/
qed. 

theorem transitive_sub: ∀h1,k1,h2,k2,A,I,J,K. 
  sub_hk h1 k1 A I J → sub_hk h2 k2 A J K → 
    sub_hk (λx.h2(h1 x)) (λx.k1(k2 x)) A I K.
#h1 #k1 #h2 #k2 #A #I #J #K #sub1 #sub2 #i #lti #fi 
cases(sub1 i lti fi) * #lth1i #fh1i #ei 
cases(sub2 (h1 i) lth1i fh1i) * #H1 #H2 #H3 % // % // 
qed. 

theorem bigop_iso: ∀n1,n2,p1,p2,B.∀nil.∀op:ACop B nil.∀f1,f2.
  iso B (mk_range B f1 n1 p1) (mk_range B f2 n2 p2) →
  \big[op,nil]_{i<n1|p1 i}(f1 i) = \big[op,nil]_{i<n2|p2 i}(f2 i).
#n1 #n2 #p1 #p2 #B #nil #op #f1 #f2 * #h * #k * * #same
@(le_gen ? n1) #i lapply p2 (elim i) 
  [(elim n2) // #m #Hind #p2 #_ #sub1 #sub2
   >bigop_Sfalse 
    [@(Hind ? (le_O_n ?)) [/2/ | @(transitive_sub … (sub_lt …) sub2) //]
    |@(sub0_to_false … sub2) //
    ]
  |#n #Hind #p2 #ltn #sub1 #sub2 (cut (n ≤n1)) [/2/] #len
   cases(true_or_false (p1 n)) #p1n
    [>bigop_Strue // (cases (sub1 n (le_n …) p1n)) * #hn #p2hn #eqn
     >(bigop_diff … (h n) n2) // >same // 
     @eq_f @(Hind ? len)
      [#i #ltin #p1i (cases (sub1 i (le_S … ltin) p1i)) * 
       #h1i #p2h1i #eqi % // % // >not_eq_to_eqb_false normalize // 
       @(not_to_not ??? (lt_to_not_eq ? ? ltin)) // 
      |#j #ltj #p2j (cases (sub2 j ltj (andb_true_r …p2j))) * 
       #ltkj #p1kj #eqj % // % // 
       (cases (le_to_or_lt_eq …(le_S_S_to_le …ltkj))) //
       #eqkj @False_ind lapply p2j @eqb_elim 
       normalize /2/
      ]
    |>bigop_Sfalse // @(Hind ? len) 
      [@(transitive_sub … (sub_lt …) sub1) //
      |#i #lti #p2i cases(sub2 i lti p2i) * #ltki #p1ki #eqi
       % // % // cases(le_to_or_lt_eq …(le_S_S_to_le …ltki)) //
       #eqki @False_ind /2/
      ]
    ]
  ]
qed.

(* commutation *)
theorem bigop_commute: ∀n,m,p11,p12,p21,p22,B.∀nil.∀op:ACop B nil.∀f.
0 < n → 0 < m →
(∀i,j. i < n → j < m → (p11 i ∧ p12 i j) = (p21 j ∧ p22 i j)) →
\big[op,nil]_{i<n|p11 i}(\big[op,nil]_{j<m|p12 i j}(f i j)) =
   \big[op,nil]_{j<m|p21 j}(\big[op,nil]_{i<n|p22 i j}(f i j)).
#n #m #p11 #p12 #p21 #p22 #B #nil #op #f #posn #posm #Heq
>bigop_prod >bigop_prod @bigop_iso 
%{(λi.(i\mod m)*n + i/m)} %{(λi.(i\mod n)*m + i/n)} % 
  [% 
    [#i #lti #Heq (* whd in ⊢ (???(?(?%?)?)); *) @eq_f2
      [@sym_eq @mod_plus_times /2 by lt_times_to_lt_div/
      |@sym_eq @div_plus_times /2 by lt_times_to_lt_div/
      ]
    |#i #lti #Hi 
     cut ((i\mod m*n+i/m)\mod n=i/m)
      [@mod_plus_times @lt_times_to_lt_div //] #H1
     cut ((i\mod m*n+i/m)/n=i \mod m)
      [@div_plus_times @lt_times_to_lt_div //] #H2
     %[%[@(lt_to_le_to_lt ? (i\mod m*n+n))
          [whd >plus_n_Sm @monotonic_le_plus_r @lt_times_to_lt_div //
          |>commutative_plus @(le_times (S(i \mod m)) m n n) // @lt_mod_m_m //
          ]
        |lapply (Heq (i/m) (i \mod m) ??)
          [@lt_mod_m_m // |@lt_times_to_lt_div //|>Hi >H1 >H2 //]
        ]
      |>H1 >H2 //
      ]
    ]
  |#i #lti #Hi 
   cut ((i\mod n*m+i/n)\mod m=i/n)
    [@mod_plus_times @lt_times_to_lt_div //] #H1
   cut ((i\mod n*m+i/n)/m=i \mod n)
    [@div_plus_times @lt_times_to_lt_div //] #H2
   %[%[@(lt_to_le_to_lt ? (i\mod n*m+m))
        [whd >plus_n_Sm @monotonic_le_plus_r @lt_times_to_lt_div //
        |>commutative_plus @(le_times (S(i \mod n)) n m m) // @lt_mod_m_m //
        ]
      |lapply (Heq (i \mod n) (i/n) ??)
        [@lt_times_to_lt_div // |@lt_mod_m_m // |>Hi >H1 >H2 //]
      ]
    |>H1 >H2 //
    ]
  ]
qed.
   
(* distributivity *)

record Dop (A:Type[0]) (nil:A): Type[0] ≝
  {sum : ACop A nil; 
   prod: A → A →A;
   null: \forall a. prod a nil = nil; 
   distr: ∀a,b,c:A. prod a (sum b c) = sum (prod a b) (prod a c)
  }.
  
theorem bigop_distr: ∀n,p,B,nil.∀R:Dop B nil.∀f,a.
  let aop ≝ sum B nil R in
  let mop ≝ prod B nil R in
  mop a \big[aop,nil]_{i<n|p i}(f i) = 
   \big[aop,nil]_{i<n|p i}(mop a (f i)).
#n #p #B #nil #R #f #a normalize (elim n) [@null]
#n #Hind (cases (true_or_false (p n))) #H
  [>bigop_Strue // >bigop_Strue // >(distr B nil R) >Hind //
  |>bigop_Sfalse // >bigop_Sfalse //
  ]
qed.
