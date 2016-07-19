include "basics/types.ma".
include "arithmetics/minimization.ma".
include "arithmetics/bigops.ma".
include "arithmetics/sigma_pi.ma".
include "arithmetics/bounded_quantifiers.ma".
include "reverse_complexity/big_O.ma".

(************************* notation for minimization *****************************)
notation "μ_{ ident i < n } p" 
  with precedence 80 for @{min $n 0 (λ${ident i}.$p)}.

notation "μ_{ ident i ≤ n } p" 
  with precedence 80 for @{min (S $n) 0 (λ${ident i}.$p)}.
  
notation "μ_{ ident i ∈ [a,b[ } p"
  with precedence 80 for @{min ($b-$a) $a (λ${ident i}.$p)}.
  
notation "μ_{ ident i ∈ [a,b] } p"
  with precedence 80 for @{min (S $b-$a) $a (λ${ident i}.$p)}.
  
(************************************ MAX *************************************)
notation "Max_{ ident i < n | p } f"
  with precedence 80
for @{'bigop $n max 0 (λ${ident i}. $p) (λ${ident i}. $f)}.

notation "Max_{ ident i < n } f"
  with precedence 80
for @{'bigop $n max 0 (λ${ident i}.true) (λ${ident i}. $f)}.

notation "Max_{ ident j ∈ [a,b[ } f"
  with precedence 80
for @{'bigop ($b-$a) max 0 (λ${ident j}.((λ${ident j}.true) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
  
notation "Max_{ ident j ∈ [a,b[ | p } f"
  with precedence 80
for @{'bigop ($b-$a) max 0 (λ${ident j}.((λ${ident j}.$p) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.

lemma Max_assoc: ∀a,b,c. max (max a b) c = max a (max b c).
#a #b #c normalize cases (true_or_false (leb a b)) #leab >leab normalize
  [cases (true_or_false (leb b c )) #lebc >lebc normalize
    [>(le_to_leb_true a c) // @(transitive_le ? b) @leb_true_to_le //
    |>leab //
    ]
  |cases (true_or_false (leb b c )) #lebc >lebc normalize //
   >leab normalize >(not_le_to_leb_false a c) // @lt_to_not_le 
   @(transitive_lt ? b) @not_le_to_lt @leb_false_to_not_le //
  ]
qed.

lemma Max0 : ∀n. max 0 n = n.
// qed.

lemma Max0r : ∀n. max n 0 = n.
#n >commutative_max //
qed.

definition MaxA ≝ 
  mk_Aop nat 0 max Max0 Max0r (λa,b,c.sym_eq … (Max_assoc a b c)). 

definition MaxAC ≝ mk_ACop nat 0 MaxA commutative_max.

lemma le_Max: ∀f,p,n,a. a < n → p a = true →
  f a ≤  Max_{i < n | p i}(f i).
#f #p #n #a #ltan #pa 
>(bigop_diff p ? 0 MaxAC f a n) // @(le_maxl … (le_n ?))
qed.

lemma le_MaxI: ∀f,p,n,m,a. m ≤ a → a < n → p a = true →
  f a ≤  Max_{i ∈ [m,n[ | p i}(f i).
#f #p #n #m #a #lema #ltan #pa 
>(bigop_diff ? ? 0 MaxAC (λi.f (i+m)) (a-m) (n-m)) 
  [<plus_minus_m_m // @(le_maxl … (le_n ?))
  |<plus_minus_m_m //
  |/2 by monotonic_lt_minus_l/
  ]
qed.

lemma Max_le: ∀f,p,n,b. 
  (∀a.a < n → p a = true → f a ≤ b) → Max_{i < n | p i}(f i) ≤ b.
#f #p #n elim n #b #H // 
#b0 #H1 cases (true_or_false (p b)) #Hb
  [>bigop_Strue [2:@Hb] @to_max [@H1 // | @H #a #ltab #pa @H1 // @le_S //]
  |>bigop_Sfalse [2:@Hb] @H #a #ltab #pa @H1 // @le_S //
  ]
qed.

(********************************** pairing ***********************************)
axiom pair: nat → nat → nat.
axiom fst : nat → nat.
axiom snd : nat → nat.

interpretation "abstract pair" 'pair f g = (pair f g). 

axiom fst_pair: ∀a,b. fst 〈a,b〉 = a.
axiom snd_pair: ∀a,b. snd 〈a,b〉 = b.
axiom surj_pair: ∀x. ∃a,b. x = 〈a,b〉. 

axiom le_fst : ∀p. fst p ≤ p.
axiom le_snd : ∀p. snd p ≤ p.
axiom le_pair: ∀a,a1,b,b1. a ≤ a1 → b ≤ b1 → 〈a,b〉 ≤ 〈a1,b1〉.

(************************************* U **************************************)
axiom U: nat → nat →nat → option nat. 

axiom monotonic_U: ∀i,x,n,m,y.n ≤m →
  U i x n = Some ? y → U i x m = Some ? y.
  
lemma unique_U: ∀i,x,n,m,yn,ym.
  U i x n = Some ? yn → U i x m = Some ? ym → yn = ym.
#i #x #n #m #yn #ym #Hn #Hm cases (decidable_le n m)
  [#lenm lapply (monotonic_U … lenm Hn) >Hm #HS destruct (HS) //
  |#ltmn lapply (monotonic_U … n … Hm) [@lt_to_le @not_le_to_lt //]
   >Hn #HS destruct (HS) //
  ]
qed.

definition code_for ≝ λf,i.∀x.
  ∃n.∀m. n ≤ m → U i x m = f x.

definition terminate ≝ λi,x,r. ∃y. U i x r = Some ? y. 

notation "{i ⊙ x} ↓ r" with precedence 60 for @{terminate $i $x $r}. 

lemma terminate_dec: ∀i,x,n. {i ⊙ x} ↓ n ∨ ¬ {i ⊙ x} ↓ n.
#i #x #n normalize cases (U i x n)
  [%2 % * #y #H destruct|#y %1 %{y} //]
qed.
  
lemma monotonic_terminate: ∀i,x,n,m.
  n ≤ m → {i ⊙ x} ↓ n → {i ⊙ x} ↓ m.
#i #x #n #m #lenm * #z #H %{z} @(monotonic_U … H) //
qed.

definition termb ≝ λi,x,t. 
  match U i x t with [None ⇒ false |Some y ⇒ true].

lemma termb_true_to_term: ∀i,x,t. termb i x t = true → {i ⊙ x} ↓ t.
#i #x #t normalize cases (U i x t) normalize [#H destruct | #y #_ %{y} //]
qed.    

lemma term_to_termb_true: ∀i,x,t. {i ⊙ x} ↓ t → termb i x t = true.
#i #x #t * #y #H normalize >H // 
qed.    

definition out ≝ λi,x,r. 
  match U i x r with [ None ⇒ 0 | Some z ⇒ z]. 

definition bool_to_nat: bool → nat ≝ 
  λb. match b with [true ⇒ 1 | false ⇒ 0]. 

coercion bool_to_nat. 

definition pU : nat → nat → nat → nat ≝ λi,x,r.〈termb i x r,out i x r〉.

lemma pU_vs_U_Some : ∀i,x,r,y. pU i x r = 〈1,y〉 ↔ U i x r = Some ? y.
#i #x #r #y % normalize
  [cases (U i x r) normalize 
    [#H cut (0=1) [lapply (eq_f … fst … H) >fst_pair >fst_pair #H @H] 
     #H1 destruct
    |#a #H cut (a=y) [lapply (eq_f … snd … H) >snd_pair >snd_pair #H1 @H1] 
     #H1 //
    ]
  |#H >H //]
qed.
  
lemma pU_vs_U_None : ∀i,x,r. pU i x r = 〈0,0〉 ↔ U i x r = None ?.
#i #x #r % normalize
  [cases (U i x r) normalize //
   #a #H cut (1=0) [lapply (eq_f … fst … H) >fst_pair >fst_pair #H1 @H1] 
   #H1 destruct
  |#H >H //]
qed.

lemma fst_pU: ∀i,x,r. fst (pU i x r) = termb i x r.
#i #x #r normalize cases (U i x r) normalize >fst_pair //
qed.

lemma snd_pU: ∀i,x,r. snd (pU i x r) = out i x r.
#i #x #r normalize cases (U i x r) normalize >snd_pair //
qed.

(********************************* the speedup ********************************)

definition min_input ≝ λh,i,x. μ_{y ∈ [S i,x] } (termb i y (h (S i) y)).

lemma min_input_def : ∀h,i,x. 
  min_input h i x = min (x -i) (S i) (λy.termb i y (h (S i) y)).
// qed.

lemma min_input_i: ∀h,i,x. x ≤ i → min_input h i x = S i.
#h #i #x #lexi >min_input_def 
cut (x - i = 0) [@sym_eq /2 by eq_minus_O/] #Hcut //
qed. 

lemma min_input_to_terminate: ∀h,i,x. 
  min_input h i x = x → {i ⊙ x} ↓ (h (S i) x).
#h #i #x #Hminx
cases (decidable_le (S i) x) #Hix
  [cases (true_or_false (termb i x (h (S i) x))) #Hcase
    [@termb_true_to_term //
    |<Hminx in Hcase; #H lapply (fmin_false (λx.termb i x (h (S i) x)) (x-i) (S i) H)
     >min_input_def in Hminx; #Hminx >Hminx in ⊢ (%→?); 
     <plus_n_Sm <plus_minus_m_m [2: @lt_to_le //]
     #Habs @False_ind /2/
    ]
  |@False_ind >min_input_i in Hminx; 
    [#eqix >eqix in Hix; * /2/ | @le_S_S_to_le @not_le_to_lt //]
  ]
qed.

lemma min_input_to_lt: ∀h,i,x. 
  min_input h i x = x → i < x.
#h #i #x #Hminx cases (decidable_le (S i) x) // 
#ltxi @False_ind >min_input_i in Hminx; 
  [#eqix >eqix in ltxi; * /2/ | @le_S_S_to_le @not_le_to_lt //]
qed.

lemma le_to_min_input: ∀h,i,x,x1. x ≤ x1 →
  min_input h i x = x → min_input h i x1 = x.
#h #i #x #x1 #lex #Hminx @(min_exists … (le_S_S … lex)) 
  [@(fmin_true … (sym_eq … Hminx)) //
  |@(min_input_to_lt … Hminx)
  |#j #H1 <Hminx @lt_min_to_false //
  |@plus_minus_m_m @le_S_S @(transitive_le … lex) @lt_to_le 
   @(min_input_to_lt … Hminx)
  ]
qed.
  
definition g ≝ λh,u,x. 
  S (max_{i ∈[u,x[ | eqb (min_input h i x) x} (out i x (h (S i) x))).
  
lemma g_def : ∀h,u,x. g h u x =
  S (max_{i ∈[u,x[ | eqb (min_input h i x) x} (out i x (h (S i) x))).
// qed.

lemma le_u_to_g_1 : ∀h,u,x. x ≤ u → g h u x = 1.
#h #u #x #lexu >g_def cut (x-u = 0) [/2 by minus_le_minus_minus_comm/]
#eq0 >eq0 normalize // qed.

lemma g_lt : ∀h,i,x. min_input h i x = x →
  out i x (h (S i) x) < g h 0 x.
#h #i #x #H @le_S_S @(le_MaxI … i) /2 by min_input_to_lt/  
qed.

(*
axiom ax1: ∀h,i.
   (∃y.i < y ∧ (termb i y (h (S i) y)=true)) ∨ 
    ∀y. i < y → (termb i y (h (S i) y)=false).

lemma eventually_0: ∀h,u.∃nu.∀x. nu < x → 
  max_{i ∈ [0,u[ | eqb (min_input h i x) x} (out i x (h (S i) x)) = 0.
#h #u elim u
  [%{0} normalize //
  |#u0 * #nu0 #Hind cases (ax1 h u0) 
    [* #x0 * #leu0x0 #Hx0 %{(max nu0 x0)}
     #x #Hx >bigop_Sfalse
      [>(minus_n_O u0) @Hind @(le_to_lt_to_lt … Hx) /2 by le_maxl/
      |@not_eq_to_eqb_false % #Hf @(absurd (x ≤ x0)) 
        [<Hf @true_to_le_min //
        |@lt_to_not_le @(le_to_lt_to_lt … Hx) /2 by le_maxl/
        ]
      ]
    |#H %{(max u0 nu0)} #x #Hx >bigop_Sfalse
      [>(minus_n_O u0) @Hind @(le_to_lt_to_lt … Hx) @le_maxr //
      |@not_eq_to_eqb_false >min_input_def
       >(min_not_exists (λy.(termb (u0+0) y (h (S (u0+0)) y)))) 
        [<plus_n_O <plus_n_Sm <plus_minus_m_m 
          [% #H1 /2/ 
          |@lt_to_le @(le_to_lt_to_lt … Hx) @le_maxl //
          ]
        |/2 by /
        ]
      ]
    ]
  ]
qed.

definition almost_equal ≝ λf,g:nat → nat. ∃nu.∀x. nu < x → f x = g x.

definition almost_equal1 ≝ λf,g:nat → nat. ¬ ∀nu.∃x. nu < x ∧ f x ≠ g x.

interpretation "almost equal" 'napart f g = (almost_equal f g). 

lemma condition_1: ∀h,u.g h 0 ≈ g h u.
#h #u cases (eventually_0 h u) #nu #H %{(max u nu)} #x #Hx @(eq_f ?? S)
>(bigop_sumI 0 u x (λi:ℕ.eqb (min_input h i x) x) nat  0 MaxA)
  [>H // @(le_to_lt_to_lt …Hx) /2 by le_maxl/
  |@lt_to_le @(le_to_lt_to_lt …Hx) /2 by le_maxr/
  |//
  ]
qed. *)

lemma max_neq0 : ∀a,b. max a b ≠ 0 → a ≠ 0 ∨ b ≠ 0.
#a #b whd in match (max a b); cases (true_or_false (leb a b)) #Hcase >Hcase
  [#H %2 @H | #H %1 @H]  
qed.

definition almost_equal ≝ λf,g:nat → nat. ¬ ∀nu.∃x. nu < x ∧ f x ≠ g x.
interpretation "almost equal" 'napart f g = (almost_equal f g). 

lemma eventually_cancelled: ∀h,u.¬∀nu.∃x. nu < x ∧
  max_{i ∈ [0,u[ | eqb (min_input h i x) x} (out i x (h (S i) x)) ≠ 0.
#h #u elim u
  [normalize % #H cases (H u) #x * #_ * #H1 @H1 //
  |#u0 @not_to_not #Hind #nu cases (Hind nu) #x * #ltx
   cases (true_or_false (eqb (min_input h (u0+O) x) x)) #Hcase 
    [>bigop_Strue [2:@Hcase] #Hmax cases (max_neq0 … Hmax) -Hmax
      [2: #H %{x} % // <minus_n_O @H]
     #Hneq0 (* if x is not enough we retry with nu=x *)
     cases (Hind x) #x1 * #ltx1 
     >bigop_Sfalse 
      [#H %{x1} % [@transitive_lt //| <minus_n_O @H]
      |@not_eq_to_eqb_false >(le_to_min_input … (eqb_true_to_eq … Hcase))
        [@lt_to_not_eq @ltx1 | @lt_to_le @ltx1]
      ]  
    |>bigop_Sfalse [2:@Hcase] #H %{x} % // <minus_n_O @H
    ]
  ]
qed.

lemma condition_1: ∀h,u.g h 0 ≈ g h u.
#h #u @(not_to_not … (eventually_cancelled h u))
#H #nu cases (H (max u nu)) #x * #ltx #Hdiff 
%{x} % [@(le_to_lt_to_lt … ltx) @(le_maxr … (le_n …))] @(not_to_not … Hdiff) 
#H @(eq_f ?? S) >(bigop_sumI 0 u x (λi:ℕ.eqb (min_input h i x) x) nat  0 MaxA) 
  [>H // |@lt_to_le @(le_to_lt_to_lt …ltx) /2 by le_maxr/ |//]
qed.

(******************************** Condition 2 *********************************)
definition total ≝ λf.λx:nat. Some nat (f x).
  
lemma exists_to_exists_min: ∀h,i. (∃x. i < x ∧ {i ⊙ x} ↓ h (S i) x) → ∃y. min_input h i y = y.
#h #i * #x * #ltix #Hx %{(min_input h i x)} @min_spec_to_min @found //
  [@(f_min_true (λy:ℕ.termb i y (h (S i) y))) %{x} % [% // | @term_to_termb_true //]
  |#y #leiy #lty @(lt_min_to_false ????? lty) //
  ]
qed.

lemma condition_2: ∀h,i. code_for (total (g h 0)) i → ¬∃x. i<x ∧ {i ⊙ x} ↓ h (S i) x.
#h #i whd in ⊢(%→?); #H % #H1 cases (exists_to_exists_min … H1) #y #Hminy
lapply (g_lt … Hminy)
lapply (min_input_to_terminate … Hminy) * #r #termy
cases (H y) -H #ny #Hy 
cut (r = g h 0 y) [@(unique_U … ny … termy) @Hy //] #Hr
whd in match (out ???); >termy >Hr  
#H @(absurd ? H) @le_to_not_lt @le_n
qed.


(********************** complexity ***********************)

(* We assume operations have a minimal structural complexity MSC. 
For instance, for time complexity, MSC is equal to the size of input.
For space complexity, MSC is typically 0, since we only measure the
space required in addition to dimension of the input. *)

axiom MSC : nat → nat.
axiom MSC_le: ∀n. MSC n ≤ n.
axiom monotonic_MSC: monotonic ? le MSC.
axiom MSC_pair: ∀a,b. MSC 〈a,b〉 ≤ MSC a + MSC b.

(* C s i means i is running in O(s) *)
 
definition C ≝ λs,i.∃c.∃a.∀x.a ≤ x → ∃y. 
  U i x (c*(s x)) = Some ? y.

(* C f s means f ∈ O(s) where MSC ∈O(s) *)
definition CF ≝ λs,f.O s MSC ∧ ∃i.code_for (total f) i ∧ C s i.
 
lemma ext_CF : ∀f,g,s. (∀n. f n = g n) → CF s f → CF s g.
#f #g #s #Hext * #HO  * #i * #Hcode #HC % // %{i} %
  [#x cases (Hcode x) #a #H %{a} whd in match (total ??); <Hext @H | //] 
qed.

(* lemma ext_CF_total : ∀f,g,s. (∀n. f n = g n) → CF s (total f) → CF s (total g).
#f #g #s #Hext * #HO * #i * #Hcode #HC % // %{i} % [2:@HC]
#x cases (Hcode x) #a #H %{a} #m #leam >(H m leam) normalize @eq_f @Hext
qed. *)

lemma monotonic_CF: ∀s1,s2,f.(∀x. s1 x ≤  s2 x) → CF s1 f → CF s2 f.
#s1 #s2 #f #H * #HO * #i * #Hcode #Hs1 % 
  [cases HO #c * #a -HO #HO %{c} %{a} #n #lean @(transitive_le … (HO n lean))
   @le_times // 
  |%{i} % [//] cases Hs1 #c * #a -Hs1 #Hs1 %{c} %{a} #n #lean 
   cases(Hs1 n lean) #y #Hy %{y} @(monotonic_U …Hy) @le_times // 
  ]
qed.

lemma O_to_CF: ∀s1,s2,f.O s2 s1 → CF s1 f → CF s2 f.
#s1 #s2 #f #H * #HO * #i * #Hcode #Hs1 % 
  [@(O_trans … H) //
  |%{i} % [//] cases Hs1 #c * #a -Hs1 #Hs1 
   cases H #c1 * #a1 #Ha1 %{(c*c1)} %{(a+a1)} #n #lean 
   cases(Hs1 n ?) [2:@(transitive_le … lean) //] #y #Hy %{y} @(monotonic_U …Hy)
   >associative_times @le_times // @Ha1 @(transitive_le … lean) //
  ]
qed.

lemma timesc_CF: ∀s,f,c.CF (λx.c*s x) f → CF s f.
#s #f #c @O_to_CF @O_times_c 
qed.

(********************************* composition ********************************)
axiom CF_comp: ∀f,g,sf,sg,sh. CF sg g → CF sf f → 
  O sh (λx. sg x + sf (g x)) → CF sh (f ∘ g).
  
lemma CF_comp_ext: ∀f,g,h,sh,sf,sg. CF sg g → CF sf f → 
  (∀x.f(g x) = h x) → O sh (λx. sg x + sf (g x)) → CF sh h.
#f #g #h #sh #sf #sg #Hg #Hf #Heq #H @(ext_CF (f ∘ g))
  [#n normalize @Heq | @(CF_comp … H) //]
qed.

(*
lemma CF_comp1: ∀f,g,s. CF s (total g) → CF s (total f) → 
  CF s (total (f ∘ g)).
#f #g #s #Hg #Hf @(timesc_CF … 2) @(monotonic_CF … (CF_comp … Hg Hf))
*)

(*
axiom CF_comp_ext2: ∀f,g,h,sf,sh. CF sh (total g) → CF sf (total f) → 
  (∀x.f(g x) = h x) → 
  (∀x. sf (g x) ≤ sh x) → CF sh (total h). 

lemma main_MSC: ∀h,f. CF h f → O h (λx.MSC (f x)). 
 
axiom CF_S: CF MSC S.
axiom CF_fst: CF MSC fst.
axiom CF_snd: CF MSC snd.

lemma CF_compS: ∀h,f. CF h f → CF h (S ∘ f).
#h #f #Hf @(CF_comp … Hf CF_S) @O_plus // @main_MSC //
qed. 

lemma CF_comp_fst: ∀h,f. CF h (total f) → CF h (total (fst ∘ f)).
#h #f #Hf @(CF_comp … Hf CF_fst) @O_plus // @main_MSC //
qed.

lemma CF_comp_snd: ∀h,f. CF h (total f) → CF h (total (snd ∘ f)).
#h #f #Hf @(CF_comp … Hf CF_snd) @O_plus // @main_MSC //
qed. *)

definition id ≝ λx:nat.x.

axiom CF_id: CF MSC id.
axiom CF_compS: ∀h,f. CF h f → CF h (S ∘ f).
axiom CF_comp_fst: ∀h,f. CF h f → CF h (fst ∘ f).
axiom CF_comp_snd: ∀h,f. CF h f → CF h (snd ∘ f). 
axiom CF_comp_pair: ∀h,f,g. CF h f → CF h g → CF h (λx. 〈f x,g x〉). 

lemma CF_fst: CF MSC fst.
@(ext_CF (fst ∘ id)) [#n //] @(CF_comp_fst … CF_id)
qed.

lemma CF_snd: CF MSC snd.
@(ext_CF (snd ∘ id)) [#n //] @(CF_comp_snd … CF_id)
qed.

(************************************** eqb ***********************************)
(* definition btotal ≝ 
  λf.λx:nat. match f x with [true ⇒ Some ? 0 |false ⇒ Some ? 1]. *)
  
axiom CF_eqb: ∀h,f,g.
  CF h f → CF h g → CF h (λx.eqb (f x) (g x)).

(* 
axiom eqb_compl2: ∀h,f,g.
  CF2 h (total2 f) → CF2 h (total2 g) → 
    CF2 h (btotal2 (λx1,x2.eqb (f x1 x2) (g x1 x2))).

axiom eqb_min_input_compl:∀h,x. 
   CF (λi.∑_{y ∈ [S i,S x[ }(h i y))
   (btotal (λi.eqb (min_input h i x) x)). *)
(*********************************** maximum **********************************) 

axiom CF_max: ∀a,b.∀p:nat →bool.∀f,ha,hb,hp,hf,s.
  CF ha a → CF hb b → CF hp p → CF hf f → 
  O s (λx.ha x + hb x + ∑_{i ∈[a x ,b x[ }(hp 〈i,x〉 + hf 〈i,x〉)) →
  CF s (λx.max_{i ∈[a x,b x[ | p 〈i,x〉 }(f 〈i,x〉)). 

(******************************** minimization ********************************) 

axiom CF_mu: ∀a,b.∀f:nat →bool.∀sa,sb,sf,s.
  CF sa a → CF sb b → CF sf f → 
  O s (λx.sa x + sb x + ∑_{i ∈[a x ,S(b x)[ }(sf 〈i,x〉)) →
  CF s (λx.μ_{i ∈[a x,b x] }(f 〈i,x〉)).

(****************************** constructibility ******************************)
 
definition constructible ≝ λs. CF s s.

lemma constr_comp : ∀s1,s2. constructible s1 → constructible s2 →
  (∀x. x ≤ s2 x) → constructible (s2 ∘ s1).
#s1 #s2 #Hs1 #Hs2 #Hle @(CF_comp … Hs1 Hs2) @O_plus @le_to_O #x [@Hle | //] 
qed.

lemma ext_constr: ∀s1,s2. (∀x.s1 x = s2 x) → 
  constructible s1 → constructible s2.
#s1 #s2 #Hext #Hs1 @(ext_CF … Hext) @(monotonic_CF … Hs1)  #x >Hext //
qed. 

(********************************* simulation *********************************)

axiom sU : nat → nat. 

axiom monotonic_sU: ∀i1,i2,x1,x2,s1,s2. i1 ≤ i2 → x1 ≤ x2 → s1 ≤ s2 →
  sU 〈i1,〈x1,s1〉〉 ≤ sU 〈i2,〈x2,s2〉〉.

lemma monotonic_sU_aux : ∀x1,x2. fst x1 ≤ fst x2 → fst (snd x1) ≤ fst (snd x2) →
snd (snd x1) ≤ snd (snd x2) → sU x1 ≤ sU x2.
#x1 #x2 cases (surj_pair x1) #a1 * #y #eqx1 >eqx1 -eqx1 cases (surj_pair y) 
#b1 * #c1 #eqy >eqy -eqy
cases (surj_pair x2) #a2 * #y2 #eqx2 >eqx2 -eqx2 cases (surj_pair y2) 
#b2 * #c2 #eqy2 >eqy2 -eqy2 >fst_pair >snd_pair >fst_pair >snd_pair 
>fst_pair >snd_pair >fst_pair >snd_pair @monotonic_sU
qed.
  
axiom sU_le: ∀i,x,s. s ≤ sU 〈i,〈x,s〉〉.
axiom sU_le_i: ∀i,x,s. MSC i ≤ sU 〈i,〈x,s〉〉.
axiom sU_le_x: ∀i,x,s. MSC x ≤ sU 〈i,〈x,s〉〉.

definition pU_unary ≝ λp. pU (fst p) (fst (snd p)) (snd (snd p)).

axiom CF_U : CF sU pU_unary.

definition termb_unary ≝ λx:ℕ.termb (fst x) (fst (snd x)) (snd (snd x)).
definition out_unary ≝ λx:ℕ.out (fst x) (fst (snd x)) (snd (snd x)).

lemma CF_termb: CF sU termb_unary. 
@(ext_CF (fst ∘ pU_unary)) [2: @CF_comp_fst @CF_U]
#n whd in ⊢ (??%?); whd in  ⊢ (??(?%)?); >fst_pair % 
qed.

lemma CF_out: CF sU out_unary. 
@(ext_CF (snd ∘ pU_unary)) [2: @CF_comp_snd @CF_U]
#n whd in ⊢ (??%?); whd in  ⊢ (??(?%)?); >snd_pair % 
qed.

(*
lemma CF_termb_comp: ∀f.CF (sU ∘ f) (termb_unary ∘ f).
#f @(CF_comp … CF_termb) *)
  
(******************** complexity of g ********************)

definition unary_g ≝ λh.λux. g h (fst ux) (snd ux).
definition auxg ≝ 
  λh,ux. max_{i ∈[fst ux,snd ux[ | eqb (min_input h i (snd ux)) (snd ux)} 
    (out i (snd ux) (h (S i) (snd ux))).

lemma compl_g1 : ∀h,s. CF s (auxg h) → CF s (unary_g h).
#h #s #H1 @(CF_compS ? (auxg h) H1) 
qed.

definition aux1g ≝ 
  λh,ux. max_{i ∈[fst ux,snd ux[ | (λp. eqb (min_input h (fst p) (snd (snd p))) (snd (snd p))) 〈i,ux〉} 
    ((λp.out (fst p) (snd (snd p)) (h (S (fst p)) (snd (snd p)))) 〈i,ux〉).

lemma eq_aux : ∀h,x.aux1g h x = auxg h x.
#h #x @same_bigop
  [#n #_ >fst_pair >snd_pair // |#n #_ #_ >fst_pair >snd_pair //]
qed.

lemma compl_g2 : ∀h,s1,s2,s. 
  CF s1
    (λp:ℕ.eqb (min_input h (fst p) (snd (snd p))) (snd (snd p))) →
  CF s2
    (λp:ℕ.out (fst p) (snd (snd p)) (h (S (fst p)) (snd (snd p)))) →
  O s (λx.MSC x + ∑_{i ∈[fst x ,snd x[ }(s1 〈i,x〉+s2 〈i,x〉)) → 
  CF s (auxg h).
#h #s1 #s2 #s #Hs1 #Hs2 #HO @(ext_CF (aux1g h)) 
  [#n whd in ⊢ (??%%); @eq_aux]
@(CF_max … CF_fst CF_snd Hs1 Hs2 …) @(O_trans … HO) 
@O_plus [@O_plus @O_plus_l // | @O_plus_r //]
qed.  

lemma compl_g3 : ∀h,s.
  CF s (λp:ℕ.min_input h (fst p) (snd (snd p))) →
  CF s (λp:ℕ.eqb (min_input h (fst p) (snd (snd p))) (snd (snd p))).
#h #s #H @(CF_eqb … H) @(CF_comp … CF_snd CF_snd) @(O_trans … (proj1 … H))
@O_plus // %{1} %{0} #n #_ >commutative_times <times_n_1 @monotonic_MSC //
qed.

definition min_input_aux ≝ λh,p.
  μ_{y ∈ [S (fst p),snd (snd p)] } 
    ((λx.termb (fst (snd x)) (fst x) (h (S (fst (snd x))) (fst x))) 〈y,p〉). 
    
lemma min_input_eq : ∀h,p. 
    min_input_aux h p  =
    min_input h (fst p) (snd (snd p)).
#h #p >min_input_def whd in ⊢ (??%?); >minus_S_S @min_f_g #i #_ #_ 
whd in ⊢ (??%%); >fst_pair >snd_pair //
qed.

definition termb_aux ≝ λh.
  termb_unary ∘ λp.〈fst (snd p),〈fst p,h (S (fst (snd p))) (fst p)〉〉.

(*
lemma termb_aux : ∀h,p.
  (λx:ℕ.termb (fst x) (fst (snd x)) (snd (snd x))) 
    〈fst (snd p),〈fst p,h (S (fst (snd p))) (fst p)〉〉 =
  termb (fst (snd p)) (fst p) (h (S (fst (snd p))) (fst p)) .
#h #p normalize >fst_pair >snd_pair >fst_pair >snd_pair // 
qed. *)

lemma compl_g4 : ∀h,s1,s.
  (CF s1 
    (λp.termb (fst (snd p)) (fst p) (h (S (fst (snd p))) (fst p)))) →
   (O s (λx.MSC x + ∑_{i ∈[S(fst x) ,S(snd (snd x))[ }(s1 〈i,x〉))) →
  CF s (λp:ℕ.min_input h (fst p) (snd (snd p))).
#h #s1 #s #Hs1 #HO @(ext_CF (min_input_aux h))
 [#n whd in ⊢ (??%%); @min_input_eq]
@(CF_mu … MSC MSC … Hs1) 
  [@CF_compS @CF_fst 
  |@CF_comp_snd @CF_snd
  |@(O_trans … HO) @O_plus [@O_plus @O_plus_l // | @O_plus_r //]
(* @(ext_CF (btotal (termb_aux h)))
  [#n normalize >fst_pair >snd_pair >fst_pair >snd_pair // ]
@(CF_compb … CF_termb) *)
qed.

(************************* a couple of technical lemmas ***********************)
lemma minus_to_0: ∀a,b. a ≤ b → minus a b = 0.
#a elim a // #n #Hind * 
  [#H @False_ind /2 by absurd/ | #b normalize #H @Hind @le_S_S_to_le /2/]
qed.

lemma sigma_bound:  ∀h,a,b. monotonic nat le h → 
  ∑_{i ∈ [a,S b[ }(h i) ≤  (S b-a)*h b.
#h #a #b #H cases (decidable_le a b) 
  [#leab cut (b = pred (S b - a + a)) 
    [<plus_minus_m_m // @le_S //] #Hb >Hb in match (h b);
   generalize in match (S b -a);
   #n elim n 
    [//
    |#m #Hind >bigop_Strue [2://] @le_plus 
      [@H @le_n |@(transitive_le … Hind) @le_times [//] @H //]
    ]
  |#ltba lapply (not_le_to_lt … ltba) -ltba #ltba
   cut (S b -a = 0) [@minus_to_0 //] #Hcut >Hcut //
  ]
qed.

lemma sigma_bound_decr:  ∀h,a,b. (∀a1,a2. a1 ≤ a2 → a2 < b → h a2 ≤ h a1) → 
  ∑_{i ∈ [a,b[ }(h i) ≤  (b-a)*h a.
#h #a #b #H cases (decidable_le a b) 
  [#leab cut ((b -a) +a ≤ b) [/2 by le_minus_to_plus_r/] generalize in match (b -a);
   #n elim n 
    [//
    |#m #Hind >bigop_Strue [2://] #Hm 
     cut (m+a ≤ b) [@(transitive_le … Hm) //] #Hm1
     @le_plus [@H // |@(transitive_le … (Hind Hm1)) //]
    ]
  |#ltba lapply (not_le_to_lt … ltba) -ltba #ltba
   cut (b -a = 0) [@minus_to_0 @lt_to_le @ltba] #Hcut >Hcut //
  ]
qed. 

lemma coroll: ∀s1:nat→nat. (∀n. monotonic ℕ le (λa:ℕ.s1 〈a,n〉)) → 
O (λx.(snd (snd x)-fst x)*(s1 〈snd (snd x),x〉)) 
  (λx.∑_{i ∈[S(fst x) ,S(snd (snd x))[ }(s1 〈i,x〉)).
#s1 #Hs1 %{1} %{0} #n #_ >commutative_times <times_n_1 
@(transitive_le … (sigma_bound …)) [@Hs1|>minus_S_S //]
qed.

lemma coroll2: ∀s1:nat→nat. (∀n,a,b. a ≤ b → b < snd n → s1 〈b,n〉 ≤ s1 〈a,n〉) → 
O (λx.(snd x - fst x)*s1 〈fst x,x〉) (λx.∑_{i ∈[fst x,snd x[ }(s1 〈i,x〉)).
#s1 #Hs1 %{1} %{0} #n #_ >commutative_times <times_n_1 
@(transitive_le … (sigma_bound_decr …)) [2://] @Hs1 
qed.

lemma compl_g5 : ∀h,s1.(∀n. monotonic ℕ le (λa:ℕ.s1 〈a,n〉)) →
  (CF s1 
    (λp.termb (fst (snd p)) (fst p) (h (S (fst (snd p))) (fst p)))) →
  CF (λx.MSC x + (snd (snd x)-fst x)*s1 〈snd (snd x),x〉) 
    (λp:ℕ.min_input h (fst p) (snd (snd p))).
#h #s1 #Hmono #Hs1 @(compl_g4 … Hs1) @O_plus 
[@O_plus_l // |@O_plus_r @coroll @Hmono]
qed.

(*
axiom compl_g6: ∀h.
  (* constructible (λx. h (fst x) (snd x)) → *)
  (CF (λx. max (MSC x) (sU 〈fst (snd x),〈fst x,h (S (fst (snd x))) (fst x)〉〉))
    (λp.termb (fst (snd p)) (fst p) (h (S (fst (snd p))) (fst p)))).
*)

lemma compl_g6: ∀h.
  constructible (λx. h (fst x) (snd x)) →
  (CF (λx. sU 〈max (fst (snd x)) (snd (snd x)),〈fst x,h (S (fst (snd x))) (fst x)〉〉) 
    (λp.termb (fst (snd p)) (fst p) (h (S (fst (snd p))) (fst p)))).
#h #hconstr @(ext_CF (termb_aux h))
  [#n normalize >fst_pair >snd_pair >fst_pair >snd_pair // ]
@(CF_comp … (λx.MSC x + h (S (fst (snd x))) (fst x)) … CF_termb) 
  [@CF_comp_pair
    [@CF_comp_fst @(monotonic_CF … CF_snd) #x //
    |@CF_comp_pair
      [@(monotonic_CF … CF_fst) #x //
      |@(ext_CF ((λx.h (fst x) (snd x))∘(λx.〈S (fst (snd x)),fst x〉)))
        [#n normalize >fst_pair >snd_pair %]
       @(CF_comp … MSC …hconstr)
        [@CF_comp_pair [@CF_compS @CF_comp_fst // |//]
        |@O_plus @le_to_O [//|#n >fst_pair >snd_pair //]
        ]
      ]
    ]
  |@O_plus
    [@O_plus
      [@(O_trans … (λx.MSC (fst x) + MSC (max (fst (snd x)) (snd (snd x))))) 
        [%{2} %{0} #x #_ cases (surj_pair x) #a * #b #eqx >eqx
         >fst_pair >snd_pair @(transitive_le … (MSC_pair …)) 
         >distributive_times_plus @le_plus [//]
         cases (surj_pair b) #c * #d #eqb >eqb
         >fst_pair >snd_pair @(transitive_le … (MSC_pair …)) 
         whd in ⊢ (??%); @le_plus 
          [@monotonic_MSC @(le_maxl … (le_n …)) 
          |>commutative_times <times_n_1 @monotonic_MSC @(le_maxr … (le_n …))  
          ]
        |@O_plus [@le_to_O #x @sU_le_x |@le_to_O #x @sU_le_i]
        ]     
      |@le_to_O #n @sU_le
      ] 
    |@le_to_O #x @monotonic_sU // @(le_maxl … (le_n …)) ]
  ]
qed.
             
(* definition faux1 ≝ λh.
  (λx.MSC x + (snd (snd x)-fst x)*(λx.sU 〈fst (snd x),〈fst x,h (S (fst (snd x))) (fst x)〉〉) 〈snd (snd x),x〉).
  
(* complexity of min_input *)
lemma compl_g7: ∀h. 
  (∀x.MSC x≤h (S (fst (snd x))) (fst x)) →
  constructible (λx. h (fst x) (snd x)) →
  (∀n. monotonic ? le (h n)) → 
  CF (λx.MSC x + (snd (snd x)-fst x)*sU 〈fst x,〈snd (snd x),h (S (fst x)) (snd (snd x))〉〉)
    (λp:ℕ.min_input h (fst p) (snd (snd p))).
#h #hle #hcostr #hmono @(monotonic_CF … (faux1 h))
  [#n normalize >fst_pair >snd_pair //]
@compl_g5 [2:@(compl_g6 h hcostr)] #n #x #y #lexy >fst_pair >snd_pair 
>fst_pair >snd_pair @monotonic_sU // @hmono @lexy
qed.*)

definition big : nat →nat ≝ λx. 
  let m ≝ max (fst x) (snd x) in 〈m,m〉.

lemma big_def : ∀a,b. big 〈a,b〉 = 〈max a b,max a b〉.
#a #b normalize >fst_pair >snd_pair // qed.

lemma le_big : ∀x. x ≤ big x. 
#x cases (surj_pair x) #a * #b #eqx >eqx @le_pair >fst_pair >snd_pair 
[@(le_maxl … (le_n …)) | @(le_maxr … (le_n …))]
qed.

definition faux2 ≝ λh.
  (λx.MSC x + (snd (snd x)-fst x)*
    (λx.sU 〈max (fst(snd x)) (snd(snd x)),〈fst x,h (S (fst (snd x))) (fst x)〉〉) 〈snd (snd x),x〉).
 
(* proviamo con x *)
lemma compl_g7: ∀h. 
  constructible (λx. h (fst x) (snd x)) →
  (∀n. monotonic ? le (h n)) → 
  CF (λx.MSC x + (snd (snd x)-fst x)*sU 〈max (fst x) (snd x),〈snd (snd x),h (S (fst x)) (snd (snd x))〉〉)
    (λp:ℕ.min_input h (fst p) (snd (snd p))).
#h #hcostr #hmono @(monotonic_CF … (faux2 h))
  [#n normalize >fst_pair >snd_pair //]
@compl_g5 [2:@(compl_g6 h hcostr)] #n #x #y #lexy >fst_pair >snd_pair 
>fst_pair >snd_pair @monotonic_sU // @hmono @lexy
qed.

(* proviamo con x *)
lemma compl_g71: ∀h. 
  constructible (λx. h (fst x) (snd x)) →
  (∀n. monotonic ? le (h n)) → 
  CF (λx.MSC (big x) + (snd (snd x)-fst x)*sU 〈max (fst x) (snd x),〈snd (snd x),h (S (fst x)) (snd (snd x))〉〉)
    (λp:ℕ.min_input h (fst p) (snd (snd p))).
#h #hcostr #hmono @(monotonic_CF … (compl_g7 h hcostr hmono)) #x
@le_plus [@monotonic_MSC //]
cases (decidable_le (fst x) (snd(snd x))) 
  [#Hle @le_times // @monotonic_sU  
  |#Hlt >(minus_to_0 … (lt_to_le … )) [// | @not_le_to_lt @Hlt]
  ]
qed.

(*
axiom compl_g8: ∀h.
  CF (λx. sU 〈fst x,〈snd (snd x),h (S (fst x)) (snd (snd x))〉〉)
    (λp:ℕ.out (fst p) (snd (snd p)) (h (S (fst p)) (snd (snd p)))). *)

definition out_aux ≝ λh.
  out_unary ∘ λp.〈fst p,〈snd(snd p),h (S (fst p)) (snd (snd p))〉〉.

lemma compl_g8: ∀h.
  constructible (λx. h (fst x) (snd x)) →
  (CF (λx. sU 〈max (fst x) (snd x),〈snd(snd x),h (S (fst x)) (snd(snd x))〉〉) 
    (λp.out (fst p) (snd (snd p)) (h (S (fst p)) (snd (snd p))))).
#h #hconstr @(ext_CF (out_aux h))
  [#n normalize >fst_pair >snd_pair >fst_pair >snd_pair // ]
@(CF_comp … (λx.h (S (fst x)) (snd(snd x)) + MSC x) … CF_out) 
  [@CF_comp_pair
    [@(monotonic_CF … CF_fst) #x //
    |@CF_comp_pair
      [@CF_comp_snd @(monotonic_CF … CF_snd) #x //
      |@(ext_CF ((λx.h (fst x) (snd x))∘(λx.〈S (fst x),snd(snd x)〉)))
        [#n normalize >fst_pair >snd_pair %]
       @(CF_comp … MSC …hconstr)
        [@CF_comp_pair [@CF_compS // | @CF_comp_snd // ]
        |@O_plus @le_to_O [//|#n >fst_pair >snd_pair //]
        ]
      ]
    ]
  |@O_plus 
    [@O_plus 
      [@le_to_O #n @sU_le 
      |@(O_trans … (λx.MSC (max (fst x) (snd x))))
        [%{2} %{0} #x #_ cases (surj_pair x) #a * #b #eqx >eqx
         >fst_pair >snd_pair @(transitive_le … (MSC_pair …)) 
         whd in ⊢ (??%); @le_plus 
          [@monotonic_MSC @(le_maxl … (le_n …)) 
          |>commutative_times <times_n_1 @monotonic_MSC @(le_maxr … (le_n …))  
          ]
        |@le_to_O #x @(transitive_le ???? (sU_le_i … )) //
        ]
      ]
    |@le_to_O #x @monotonic_sU [@(le_maxl … (le_n …))|//|//]
  ]
qed.

(*
lemma compl_g81: ∀h.
  (∀x.MSC x≤h (S (fst x)) (snd(snd x))) →
  constructible (λx. h (fst x) (snd x)) →
  CF (λx. sU 〈max (fst x) (snd x),〈snd (snd x),h (S (fst x)) (snd (snd x))〉〉)
    (λp:ℕ.out (fst p) (snd (snd p)) (h (S (fst p)) (snd (snd p)))).
#h #hle #hconstr @(monotonic_CF ???? (compl_g8 h hle hconstr)) #x @monotonic_sU // @(le_maxl … (le_n … )) 
qed. *)

(* axiom daemon : False. *)

lemma compl_g9 : ∀h. 
  constructible (λx. h (fst x) (snd x)) →
  (∀n. monotonic ? le (h n)) → 
  (∀n,a,b. a ≤ b → b ≤ n → h b n ≤ h a n) →
  CF (λx. (S (snd x-fst x))*MSC 〈x,x〉 + 
      (snd x-fst x)*(S(snd x-fst x))*sU 〈x,〈snd x,h (S (fst x)) (snd x)〉〉)
   (auxg h).
#h #hconstr #hmono #hantimono 
@(compl_g2 h ??? (compl_g3 … (compl_g71 h hconstr hmono)) (compl_g8 h hconstr))
@O_plus 
  [@O_plus_l @le_to_O #x >(times_n_1 (MSC x)) >commutative_times @le_times
    [// | @monotonic_MSC // ]]
@(O_trans … (coroll2 ??))
  [#n #a #b #leab #ltb >fst_pair >fst_pair >snd_pair >snd_pair
   cut (b ≤ n) [@(transitive_le … (le_snd …)) @lt_to_le //] #lebn
   cut (max a n = n) 
    [normalize >le_to_leb_true [//|@(transitive_le … leab lebn)]] #maxa
   cut (max b n = n) [normalize >le_to_leb_true //] #maxb
   @le_plus
    [@le_plus [>big_def >big_def >maxa >maxb //]
     @le_times 
      [/2 by monotonic_le_minus_r/ 
      |@monotonic_sU // @hantimono [@le_S_S // |@ltb] 
      ]
    |@monotonic_sU // @hantimono [@le_S_S // |@ltb]
    ] 
  |@le_to_O #n >fst_pair >snd_pair
   cut (max (fst n) n = n) [normalize >le_to_leb_true //] #Hmax >Hmax
   >associative_plus >distributive_times_plus
   @le_plus [@le_times [@le_S // |>big_def >Hmax //] |//] 
  ]
qed.

definition sg ≝ λh,x.
  (S (snd x-fst x))*MSC 〈x,x〉 + (snd x-fst x)*(S(snd x-fst x))*sU 〈x,〈snd x,h (S (fst x)) (snd x)〉〉.

lemma sg_def : ∀h,a,b. 
  sg h 〈a,b〉 = (S (b-a))*MSC 〈〈a,b〉,〈a,b〉〉 + 
   (b-a)*(S(b-a))*sU 〈〈a,b〉,〈b,h (S a) b〉〉.
#h #a #b whd in ⊢ (??%?); >fst_pair >snd_pair // 
qed. 

lemma compl_g11 : ∀h.
  constructible (λx. h (fst x) (snd x)) →
  (∀n. monotonic ? le (h n)) → 
  (∀n,a,b. a ≤ b → b ≤ n → h b n ≤ h a n) →
  CF (sg h) (unary_g h).
#h #hconstr #Hm #Ham @compl_g1 @(compl_g9 h hconstr Hm Ham)
qed. 

(**************************** closing the argument ****************************)

let rec h_of_aux (r:nat →nat) (c,d,b:nat) on d : nat ≝ 
  match d with 
  [ O ⇒ c (* MSC 〈〈b,b〉,〈b,b〉〉 *)
  | S d1 ⇒ (S d)*(MSC 〈〈b-d,b〉,〈b-d,b〉〉) +
     d*(S d)*sU 〈〈b-d,b〉,〈b,r (h_of_aux r c d1 b)〉〉].

lemma h_of_aux_O: ∀r,c,b.
  h_of_aux r c O b  = c.
// qed.

lemma h_of_aux_S : ∀r,c,d,b. 
  h_of_aux r c (S d) b = 
    (S (S d))*(MSC 〈〈b-(S d),b〉,〈b-(S d),b〉〉) + 
      (S d)*(S (S d))*sU 〈〈b-(S d),b〉,〈b,r(h_of_aux r c d b)〉〉.
// qed.

definition h_of ≝ λr,p. 
  let m ≝ max (fst p) (snd p) in 
  h_of_aux r (MSC 〈〈m,m〉,〈m,m〉〉) (snd p - fst p) (snd p).

lemma h_of_O: ∀r,a,b. b ≤ a → 
  h_of r 〈a,b〉 = let m ≝ max a b in MSC 〈〈m,m〉,〈m,m〉〉.
#r #a #b #Hle normalize >fst_pair >snd_pair >(minus_to_0 … Hle) //
qed.

lemma h_of_def: ∀r,a,b.h_of r 〈a,b〉 = 
  let m ≝ max a b in 
  h_of_aux r (MSC 〈〈m,m〉,〈m,m〉〉) (b - a) b.
#r #a #b normalize >fst_pair >snd_pair //
qed.
  
lemma mono_h_of_aux: ∀r.(∀x. x ≤ r x) → monotonic ? le r →
  ∀d,d1,c,c1,b,b1.c ≤ c1 → d ≤ d1 → b ≤ b1 → 
  h_of_aux r c d b ≤ h_of_aux r c1 d1 b1.
#r #Hr #monor #d #d1 lapply d -d elim d1 
  [#d #c #c1 #b #b1 #Hc #Hd @(le_n_O_elim ? Hd) #leb 
   >h_of_aux_O >h_of_aux_O  //
  |#m #Hind #d #c #c1 #b #b1 #lec #led #leb cases (le_to_or_lt_eq … led)
    [#ltd @(transitive_le … (Hind … lec ? leb)) [@le_S_S_to_le @ltd]
     >h_of_aux_S @(transitive_le ???? (le_plus_n …))
     >(times_n_1 (h_of_aux r c1 m b1)) in ⊢ (?%?); 
     >commutative_times @le_times [//|@(transitive_le … (Hr ?)) @sU_le]
    |#Hd >Hd >h_of_aux_S >h_of_aux_S 
     cut (b-S m ≤ b1 - S m) [/2 by monotonic_le_minus_l/] #Hb1
     @le_plus [@le_times //] 
      [@monotonic_MSC @le_pair @le_pair //
      |@le_times [//] @monotonic_sU 
        [@le_pair // |// |@monor @Hind //]
      ]
    ]
  ]
qed.

lemma mono_h_of2: ∀r.(∀x. x ≤ r x) → monotonic ? le r →
  ∀i,b,b1. b ≤ b1 → h_of r 〈i,b〉 ≤ h_of r 〈i,b1〉.
#r #Hr #Hmono #i #a #b #leab >h_of_def >h_of_def
cut (max i a ≤ max i b)
  [@to_max 
    [@(le_maxl … (le_n …))|@(transitive_le … leab) @(le_maxr … (le_n …))]]
#Hmax @(mono_h_of_aux r Hr Hmono) 
  [@monotonic_MSC @le_pair @le_pair @Hmax |/2 by monotonic_le_minus_l/ |@leab]
qed.

axiom h_of_constr : ∀r:nat →nat. 
  (∀x. x ≤ r x) → monotonic ? le r → constructible r →
  constructible (h_of r).

lemma speed_compl: ∀r:nat →nat. 
  (∀x. x ≤ r x) → monotonic ? le r → constructible r →
  CF (h_of r) (unary_g (λi,x. r(h_of r 〈i,x〉))).
#r #Hr #Hmono #Hconstr @(monotonic_CF … (compl_g11 …)) 
  [#x cases (surj_pair x) #a * #b #eqx >eqx 
   >sg_def cases (decidable_le b a)
    [#leba >(minus_to_0 … leba) normalize in ⊢ (?%?);
     <plus_n_O <plus_n_O >h_of_def 
     cut (max a b = a) 
      [normalize cases (le_to_or_lt_eq … leba)
        [#ltba >(lt_to_leb_false … ltba) % 
        |#eqba <eqba >(le_to_leb_true … (le_n ?)) % ]]
     #Hmax >Hmax normalize >(minus_to_0 … leba) normalize
     @monotonic_MSC @le_pair @le_pair //
    |#ltab >h_of_def >h_of_def
     cut (max a b = b) 
      [normalize >(le_to_leb_true … ) [%] @lt_to_le @not_le_to_lt @ltab]
     #Hmax >Hmax 
     cut (max (S a) b = b) 
      [whd in ⊢ (??%?);  >(le_to_leb_true … ) [%] @not_le_to_lt @ltab]
     #Hmax1 >Hmax1
     cut (∃d.b - a = S d) 
       [%{(pred(b-a))} >S_pred [//] @lt_plus_to_minus_r @not_le_to_lt @ltab] 
     * #d #eqd >eqd  
     cut (b-S a = d) [//] #eqd1 >eqd1 >h_of_aux_S >eqd1 
     cut (b - S d = a) 
       [@plus_to_minus >commutative_plus @minus_to_plus 
         [@lt_to_le @not_le_to_lt // | //]] #eqd2 >eqd2
     normalize //
    ]
  |#n #a #b #leab #lebn >h_of_def >h_of_def
   cut (max a n = n) 
    [normalize >le_to_leb_true [%|@(transitive_le … leab lebn)]] #Hmaxa
   cut (max b n = n) 
    [normalize >(le_to_leb_true … lebn) %] #Hmaxb 
   >Hmaxa >Hmaxb @Hmono @(mono_h_of_aux r … Hr Hmono) // /2 by monotonic_le_minus_r/
  |#n #a #b #leab @Hmono @(mono_h_of2 … Hr Hmono … leab)
  |@(constr_comp … Hconstr Hr) @(ext_constr (h_of r))
    [#x cases (surj_pair x) #a * #b #eqx >eqx >fst_pair >snd_pair //]  
   @(h_of_constr r Hr Hmono Hconstr)
  ]
qed.

(* 
lemma unary_g_def : ∀h,i,x. g h i x = unary_g h 〈i,x〉.
#h #i #x whd in ⊢ (???%); >fst_pair >snd_pair %
qed.  *)

(* smn *)
axiom smn: ∀f,s. CF s f → ∀x. CF (λy.s 〈x,y〉) (λy.f 〈x,y〉).

lemma speed_compl_i: ∀r:nat →nat. 
  (∀x. x ≤ r x) → monotonic ? le r → constructible r →
  ∀i. CF (λx.h_of r 〈i,x〉) (λx.g (λi,x. r(h_of r 〈i,x〉)) i x).
#r #Hr #Hmono #Hconstr #i 
@(ext_CF (λx.unary_g (λi,x. r(h_of r 〈i,x〉)) 〈i,x〉))
  [#n whd in ⊢ (??%%); @eq_f @sym_eq >fst_pair >snd_pair %]
@smn @(ext_CF … (speed_compl r Hr Hmono Hconstr)) #n //
qed.

theorem pseudo_speedup: 
  ∀r:nat →nat. (∀x. x ≤ r x) → monotonic ? le r → constructible r →
  ∃f.∀sf. CF sf f → ∃g,sg. f ≈ g ∧ CF sg g ∧ O sf (r ∘ sg).
(* ∃m,a.∀n. a≤n → r(sg a) < m * sf n. *)
#r #Hr #Hmono #Hconstr
(* f is (g (λi,x. r(h_of r 〈i,x〉)) 0) *) 
%{(g (λi,x. r(h_of r 〈i,x〉)) 0)} #sf * #H * #i *
#Hcodei #HCi 
(* g is (g (λi,x. r(h_of r 〈i,x〉)) (S i)) *)
%{(g (λi,x. r(h_of r 〈i,x〉)) (S i))}
(* sg is (λx.h_of r 〈i,x〉) *)
%{(λx. h_of r 〈S i,x〉)}
lapply (speed_compl_i … Hr Hmono Hconstr (S i)) #Hg
%[%[@condition_1 |@Hg]
 |cases Hg #H1 * #j * #Hcodej #HCj
  lapply (condition_2 … Hcodei) #Hcond2 (* @not_to_not *)
  cases HCi #m * #a #Ha %{m} %{(max (S i) a)} #n #ltin @lt_to_le @not_le_to_lt 
  @(not_to_not … Hcond2) -Hcond2 #Hlesf %{n} % 
  [@(transitive_le … ltin) @(le_maxl … (le_n …))]
  cases (Ha n ?) [2: @(transitive_le … ltin) @(le_maxr … (le_n …))] 
  #y #Uy %{y} @(monotonic_U … Uy) @(transitive_le … Hlesf) //
 ]
qed.

theorem pseudo_speedup': 
  ∀r:nat →nat. (∀x. x ≤ r x) → monotonic ? le r → constructible r →
  ∃f.∀sf. CF sf f → ∃g,sg. f ≈ g ∧ CF sg g ∧ 
  (* ¬ O (r ∘ sg) sf. *)
  ∃m,a.∀n. a≤n → r(sg a) < m * sf n. 
#r #Hr #Hmono #Hconstr 
(* f is (g (λi,x. r(h_of r 〈i,x〉)) 0) *) 
%{(g (λi,x. r(h_of r 〈i,x〉)) 0)} #sf * #H * #i *
#Hcodei #HCi 
(* g is (g (λi,x. r(h_of r 〈i,x〉)) (S i)) *)
%{(g (λi,x. r(h_of r 〈i,x〉)) (S i))}
(* sg is (λx.h_of r 〈i,x〉) *)
%{(λx. h_of r 〈S i,x〉)}
lapply (speed_compl_i … Hr Hmono Hconstr (S i)) #Hg
%[%[@condition_1 |@Hg]
 |cases Hg #H1 * #j * #Hcodej #HCj
  lapply (condition_2 … Hcodei) #Hcond2 (* @not_to_not *)
  cases HCi #m * #a #Ha
  %{m} %{(max (S i) a)} #n #ltin @not_le_to_lt @(not_to_not … Hcond2) -Hcond2 #Hlesf 
  %{n} % [@(transitive_le … ltin) @(le_maxl … (le_n …))]
  cases (Ha n ?) [2: @(transitive_le … ltin) @(le_maxr … (le_n …))] 
  #y #Uy %{y} @(monotonic_U … Uy) @(transitive_le … Hlesf)
  @Hmono @(mono_h_of2 … Hr Hmono … ltin)
 ]
qed.
  