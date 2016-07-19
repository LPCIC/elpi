
include "arithmetics/nat.ma".
include "arithmetics/log.ma".
(* include "arithmetics/ord.ma". *)
include "arithmetics/bigops.ma".
include "arithmetics/bounded_quantifiers.ma".
include "arithmetics/pidgeon_hole.ma".
include "basics/sets.ma".
include "basics/types.ma".

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

lemma Max_le: ∀f,p,n,b. 
  (∀a.a < n → p a = true → f a ≤ b) → Max_{i < n | p i}(f i) ≤ b.
#f #p #n elim n #b #H // 
#b0 #H1 cases (true_or_false (p b)) #Hb
  [>bigop_Strue [2:@Hb] @to_max [@H1 // | @H #a #ltab #pa @H1 // @le_S //]
  |>bigop_Sfalse [2:@Hb] @H #a #ltab #pa @H1 // @le_S //
  ]
qed.

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

(* 
lemma O_ff: ∀f,s. O s f → O s (f+f).
#f #s #Osf /2/ 
qed. *)

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


(*********************************** pairing **********************************) 

axiom pair: nat →nat →nat.
axiom fst : nat → nat.
axiom snd : nat → nat.
axiom fst_pair: ∀a,b. fst (pair a b) = a.
axiom snd_pair: ∀a,b. snd (pair a b) = b. 

interpretation "abstract pair" 'pair f g = (pair f g).

(************************ basic complexity notions ****************************)

(* u is the deterministic configuration relation of the universal machine (one 
   step) 

axiom u: nat → option nat.

let rec U c n on n ≝ 
  match n with  
  [ O ⇒ None ?
  | S m ⇒ match u c with 
    [ None ⇒ Some ? c (* halting case *)
    | Some c1 ⇒ U c1 m
    ]
  ].
 
lemma halt_U: ∀i,n,y. u i = None ? → U i n = Some ? y → y = i.
#i #n #y #H cases n
  [normalize #H1 destruct |#m normalize >H normalize #H1 destruct //]
qed. 

lemma Some_to_halt: ∀n,i,y. U i n = Some ? y → u y = None ? .
#n elim n
  [#i #y normalize #H destruct (H)
  |#m #Hind #i #y normalize 
   cut (u i = None ? ∨ ∃c. u i = Some ? c) 
    [cases (u i) [/2/ | #c %2 /2/ ]] 
   *[#H >H normalize #H1 destruct (H1) // |* #c #H >H normalize @Hind ]
  ]
qed. *)

axiom U: nat → nat → nat → option nat. 
(*
lemma monotonici_U: ∀y,n,m,i.
  U i m = Some ? y → U i (n+m) = Some ? y.
#y #n #m elim m 
  [#i normalize #H destruct 
  |#p #Hind #i <plus_n_Sm normalize
    cut (u i = None ? ∨ ∃c. u i = Some ? c) 
    [cases (u i) [/2/ | #c %2 /2/ ]] 
   *[#H1 >H1 normalize // |* #c #H >H normalize #H1 @Hind //]
  ]
qed. *)

axiom monotonic_U: ∀i,x,n,m,y.n ≤m →
  U i x n = Some ? y → U i x m = Some ? y.
(* #i #n #m #y #lenm #H >(plus_minus_m_m m n) // @monotonici_U //
qed. *)

(* axiom U: nat → nat → option nat. *)
(* axiom monotonic_U: ∀i,n,m,y.n ≤m →
   U i n = Some ? y → U i m = Some ? y. *)
  
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
notation "[i,x] ↓ r" with precedence 60 for @{terminate $i $x $r}.

definition lang ≝ λi,x.∃r,y. U i x r = Some ? y ∧ 0  < y. 

lemma lang_cf :∀f,i,x. code_for f i → 
  lang i x ↔ ∃y.f x = Some ? y ∧ 0 < y.
#f #i #x normalize #H %
  [* #n * #y * #H1 #posy %{y} % // 
   cases (H x) -H #m #H <(H (max n m)) [2:@(le_maxr … n) //]
   @(monotonic_U … H1) @(le_maxl … m) //
  |cases (H x) -H #m #Hm * #y #Hy %{m} %{y} >Hm // 
  ]
qed.

(******************************* complexity classes ***************************)

axiom size: nat → nat.
axiom of_size: nat → nat.

interpretation "size" 'card n = (size n).

axiom size_of_size: ∀n. |of_size n| = n.
axiom monotonic_size: monotonic ? le size.

axiom of_size_max: ∀i,n. |i| = n → i ≤ of_size n.

axiom size_fst : ∀n. |fst n| ≤ |n|.

definition size_f ≝ λf,n.Max_{i < S (of_size n) | eqb (|i|) n}|(f i)|.

lemma size_f_def: ∀f,n. size_f f n = 
  Max_{i < S (of_size n) | eqb (|i|) n}|(f i)|.
// qed.

(*
definition Max_const : ∀f,p,n,a. a < n → p a →
  ∀n. f n = g n →
  Max_{i < n | p n}(f n) = *)

lemma size_f_size : ∀f,n. size_f (f ∘ size) n = |(f n)|.
#f #n @le_to_le_to_eq
  [@Max_le #a #lta #Ha normalize >(eqb_true_to_eq  … Ha) //
  |<(size_of_size n) in ⊢ (?%?); >size_f_def
   @(le_Max (λi.|f (|i|)|) ? (S (of_size n)) (of_size n) ??)
    [@le_S_S // | @eq_to_eqb_true //]
  ]
qed.

lemma size_f_id : ∀n. size_f (λx.x) n = n.
#n @le_to_le_to_eq
  [@Max_le #a #lta #Ha >(eqb_true_to_eq  … Ha) //
  |<(size_of_size n) in ⊢ (?%?); >size_f_def
   @(le_Max (λi.|i|) ? (S (of_size n)) (of_size n) ??)
    [@le_S_S // | @eq_to_eqb_true //]
  ]
qed.

lemma size_f_fst : ∀n. size_f fst n ≤ n.
#n @Max_le #a #lta #Ha <(eqb_true_to_eq  … Ha) //
qed.

(* definition def ≝ λf:nat → option nat.λx.∃y. f x = Some ? y.*)

(* C s i means that the complexity of i is O(s) *)

definition C ≝ λs,i.∃c.∃a.∀x.a ≤ |x| → ∃y. 
  U i x (c*(s(|x|))) = Some ? y.

definition CF ≝ λs,f.∃i.code_for f i ∧ C s i.

lemma ext_CF : ∀f,g,s. (∀n. f n = g n) → CF s f → CF s g.
#f #g #s #Hext * #i * #Hcode #HC %{i} %
  [#x cases (Hcode x) #a #H %{a} <Hext @H | //] 
qed. 

lemma monotonic_CF: ∀s1,s2,f. O s2 s1 → CF s1 f → CF s2 f.
#s1 #s2 #f * #c1 * #a #H * #i * #Hcodef #HCs1 %{i} % //
cases HCs1 #c2 * #b #H2 %{(c2*c1)} %{(max a b)} 
#x #Hmax cases (H2 x ?) [2:@(le_maxr … Hmax)] #y #Hy
%{y} @(monotonic_U …Hy) >associative_times @le_times // @H @(le_maxl … Hmax)
qed. 

(************************** The diagonal language *****************************)

(* the diagonal language used for the hierarchy theorem *)

definition diag ≝ λs,i. 
  U (fst i) i (s (|i|)) = Some ? 0. 

lemma equiv_diag: ∀s,i. 
  diag s i ↔ [fst i,i] ↓ s (|i|) ∧ ¬lang (fst i) i.
#s #i %
  [whd in ⊢ (%→?); #H % [%{0} //] % * #x * #y *
   #H1 #Hy cut (0 = y) [@(unique_U … H H1)] #eqy /2/
  |* * #y cases y //
   #y0 #H * #H1 @False_ind @H1 -H1 whd %{(s (|i|))} %{(S y0)} % //
  ]
qed.

(* Let us define the characteristic function diag_cf for diag, and prove
it correctness *)

definition diag_cf ≝ λs,i.
  match U (fst i) i (s (|i|)) with
  [ None ⇒ None ?
  | Some y ⇒ if (eqb y 0) then (Some ? 1) else (Some ? 0)].

lemma diag_cf_OK: ∀s,x. diag s x ↔ ∃y.diag_cf s x = Some ? y ∧ 0 < y.
#s #x % 
  [whd in ⊢ (%→?); #H %{1} % // whd in ⊢ (??%?); >H // 
  |* #y * whd in ⊢ (??%?→?→%); 
   cases (U (fst x) x (s (|x|))) normalize
    [#H destruct
    |#x cases (true_or_false (eqb x 0)) #Hx >Hx 
      [>(eqb_true_to_eq … Hx) // 
      |normalize #H destruct #H @False_ind @(absurd ? H) @lt_to_not_le //  
      ]
    ]
  ]
qed.

lemma diag_spec: ∀s,i. code_for (diag_cf s) i → ∀x. lang i x ↔ diag s x.
#s #i #Hcode #x @(iff_trans  … (lang_cf … Hcode)) @iff_sym @diag_cf_OK
qed. 

(******************************************************************************)

lemma absurd1: ∀P. iff P (¬ P) →False.
#P * #H1 #H2 cut (¬P) [% #H2 @(absurd … H2) @H1 //] 
#H3 @(absurd ?? H3) @H2 @H3 
qed.

(* axiom weak_pad : ∀a,∃a0.∀n. a0 < n → ∃b. |〈a,b〉| = n. *)
lemma weak_pad1 :∀n,a.∃b. n ≤ 〈a,b〉. 
#n #a 
cut (∀i.decidable (〈a,i〉 < n))
  [#i @decidable_le ] 
   #Hdec cases(decidable_forall (λb. 〈a,b〉 < n) Hdec n)
  [#H cut (∀i. i < n → ∃b. b < n ∧ 〈a,b〉 = i)
    [@(injective_to_exists … H) //]
   #Hcut %{n} @not_lt_to_le % #Han
   lapply(Hcut ? Han) * #x * #Hx #Hx2 
   cut (x = n) [//] #Hxn >Hxn in Hx; /2 by absurd/ 
  |#H lapply(not_forall_to_exists … Hdec H) 
   * #b * #H1 #H2 %{b} @not_lt_to_le @H2
  ]
qed. 

lemma pad : ∀n,a. ∃b. n ≤ |〈a,b〉|.
#n #a cases (weak_pad1 (of_size n) a) #b #Hb 
%{b} <(size_of_size n) @monotonic_size //
qed.

lemma o_to_ex: ∀s1,s2. o s1 s2 → ∀i. C s2 i →
  ∃b.[i, 〈i,b〉] ↓ s1 (|〈i,b〉|).
#s1 #s2  #H #i * #c * #x0 #H1 
cases (H c) #n0 #H2 cases (pad (max x0 n0) i) #b #Hmax
%{b} cases (H1 〈i,b〉 ?)
  [#z #H3 %{z} @(monotonic_U … H3) @lt_to_le @H2
   @(le_maxr … Hmax)
  |@(le_maxl … Hmax)
  ]
qed. 

lemma diag1_not_s1: ∀s1,s2. o s1 s2 → ¬ CF s2 (diag_cf s1).
#s1 #s2 #H1 % * #i * #Hcode_i #Hs2_i 
cases (o_to_ex  … H1 ? Hs2_i) #b #H2
lapply (diag_spec … Hcode_i) #H3
@(absurd1 (lang i 〈i,b〉))
@(iff_trans … (H3 〈i,b〉)) 
@(iff_trans … (equiv_diag …)) >fst_pair 
%[* #_ // |#H6 % // ]
qed.

(******************************************************************************)

definition to_Some ≝ λf.λx:nat. Some nat (f x).

definition deopt ≝ λn. match n with 
  [ None ⇒ 1
  | Some n ⇒ n].
  
definition opt_comp ≝ λf,g:nat → option nat. λx.
  match g x with 
  [ None ⇒ None ?
  | Some y ⇒ f y ].   

(* axiom CFU: ∀h,g,s. CF s (to_Some h)  → CF s (to_Some (of_size ∘ g)) → 
  CF (Slow s) (λx.U (h x) (g x)). *)
  
axiom sU2: nat → nat → nat.
axiom sU: nat → nat → nat → nat.

(* axiom CFU: CF sU (λx.U (fst x) (snd x)). *)

axiom CFU_new: ∀h,g,f,s. 
  CF s (to_Some h)  → CF s (to_Some g) → CF s (to_Some f) → 
  O s (λx. sU (size_f h x) (size_f g x) (size_f f x)) → 
  CF s (λx.U (h x) (g x) (|f x|)).
    
lemma CFU: ∀h,g,f,s1,s2,s3. 
  CF s1 (to_Some h)  → CF s2 (to_Some g) → CF s3 (to_Some f) → 
  CF (λx. s1 x + s2 x + s3 x + sU (size_f h x) (size_f g x) (size_f f x)) 
    (λx.U (h x) (g x) (|f x|)).
#h #g #f #s1 #s2 #s3 #Hh #Hg #Hf @CFU_new
  [@(monotonic_CF … Hh) @O_plus_l @O_plus_l @O_plus_l //
  |@(monotonic_CF … Hg) @O_plus_l @O_plus_l @O_plus_r //
  |@(monotonic_CF … Hf) @O_plus_l @O_plus_r //
  |@O_plus_r //
  ]
qed.
    
axiom monotonic_sU: ∀a1,a2,b1,b2,c1,c2. a1 ≤ a2 → b1 ≤ b2 → c1 ≤c2 →
  sU a1 b1 c1 ≤ sU a2 b2 c2.

axiom superlinear_sU: ∀i,x,r. r ≤ sU i x r.

definition sU_space ≝ λi,x,r.i+x+r.
definition sU_time ≝ λi,x,r.i+x+(i^2)*r*(log 2 r).

(*
axiom CF_comp: ∀f,g,s1, s2. CF s1 f → CF s2 g → 
  CF (λx.s2 x + s1 (size (deopt (g x)))) (opt_comp f g).

(* axiom CF_comp: ∀f,g,s1, s2. CF s1 f → CF s2 g → 
  CF (s1 ∘ (λx. size (deopt (g x)))) (opt_comp f g). *)
  
axiom CF_comp_strong: ∀f,g,s1,s2. CF s1 f → CF s2 g → 
  CF (s1 ∘ s2) (opt_comp f g). *)

definition IF ≝ λb,f,g:nat →option nat. λx.
  match b x with 
  [None ⇒ None ?
  |Some n ⇒ if (eqb n 0) then f x else g x].
  
axiom IF_CF_new: ∀b,f,g,s. CF s b → CF s f → CF s g → CF s (IF b f g).

lemma IF_CF: ∀b,f,g,sb,sf,sg. CF sb b → CF sf f → CF sg g → 
  CF (λn. sb n + sf n + sg n) (IF b f g).
#b #f #g #sb #sf #sg #Hb #Hf #Hg @IF_CF_new
  [@(monotonic_CF … Hb) @O_plus_l @O_plus_l //
  |@(monotonic_CF … Hf) @O_plus_l @O_plus_r //
  |@(monotonic_CF … Hg) @O_plus_r //
  ]
qed.

lemma diag_cf_def : ∀s.∀i. 
  diag_cf s i =  
    IF (λi.U (fst i) i (|of_size (s (|i|))|)) (λi.Some ? 1) (λi.Some ? 0) i.
#s #i normalize >size_of_size // qed. 

(* and now ... *)
axiom CF_pair: ∀f,g,s. CF s (λx.Some ? (f x)) → CF s (λx.Some ? (g x)) → 
  CF s (λx.Some ? (pair (f x) (g x))).

axiom CF_fst: ∀f,s. CF s (λx.Some ? (f x)) → CF s (λx.Some ? (fst (f x))).

definition minimal ≝ λs. CF s (λn. Some ? n) ∧ ∀c. CF s (λn. Some ? c).


(*
axiom le_snd: ∀n. |snd n| ≤ |n|.
axiom daemon: ∀P:Prop.P. *)

definition constructible ≝ λs. CF s (λx.Some ? (of_size (s (|x|)))).

lemma diag_s: ∀s. minimal s → constructible s → 
  CF (λx.sU x x (s x)) (diag_cf s).
#s * #Hs_id #Hs_c #Hs_constr 
cut (O (λx:ℕ.sU x x (s x)) s) [%{1} %{0} #n //]
#O_sU_s @ext_CF [2: #n @sym_eq @diag_cf_def | skip]
@IF_CF_new [2,3:@(monotonic_CF … (Hs_c ?)) // ] 
@CFU_new
  [@CF_fst @(monotonic_CF … Hs_id) //
  |@(monotonic_CF … Hs_id) //
  |@(monotonic_CF … Hs_constr) //
  |%{1} %{0} #n #_ >commutative_times <times_n_1
   @monotonic_sU // >size_f_size >size_of_size //
  ]
qed. 

(*
lemma diag_s: ∀s. minimal s → constructible s → 
  CF (λx.s x + sU x x (s x)) (diag_cf s).
#s * #Hs_id #Hs_c #Hs_constr 
@ext_CF [2: #n @sym_eq @diag_cf_def | skip]
@IF_CF_new [2,3:@(monotonic_CF … (Hs_c ?)) @O_plus_l //]
@CFU_new
  [@CF_fst @(monotonic_CF … Hs_id) @O_plus_l //
  |@(monotonic_CF … Hs_id) @O_plus_l //
  |@(monotonic_CF … Hs_constr) @O_plus_l //
  |@O_plus_r %{1} %{0} #n #_ >commutative_times <times_n_1
   @monotonic_sU // >size_f_size >size_of_size //
  ]
qed. *)

(* proof with old axioms
lemma diag_s: ∀s. minimal s → constructible s → 
  CF (λx.s x + sU x x (s x)) (diag_cf s).
#s * #Hs_id #Hs_c #Hs_constr 
@ext_CF [2: #n @sym_eq @diag_cf_def | skip]
@(monotonic_CF ???? (IF_CF (λi:ℕ.U (pair (fst i) i) (|of_size (s (|i|))|))
   … (λi.s i + s i + s i + (sU (size_f fst i) (size_f (λi.i) i) (size_f (λi.of_size (s (|i|))) i))) … (Hs_c 1) (Hs_c 0) … ))
  [2: @CFU [@CF_fst // | // |@Hs_constr]
  |@(O_ext2 (λn:ℕ.s n+sU (size_f fst n) n (s n) + (s n+s n+s n+s n))) 
    [2: #i >size_f_size >size_of_size >size_f_id //] 
   @O_absorbr 
    [%{1} %{0} #n #_ >commutative_times <times_n_1 @le_plus //
     @monotonic_sU // 
    |@O_plus_l @(O_plus … (O_refl s)) @(O_plus … (O_refl s)) 
     @(O_plus … (O_refl s)) //
  ]
qed.
*)

(*************************** The hierachy theorem *****************************)

(*
theorem hierarchy_theorem_right: ∀s1,s2:nat→nat. 
  O s1 idN → constructible s1 →
    not_O s2 s1 → ¬ CF s1 ⊆ CF s2.
#s1 #s2 #Hs1 #monos1 #H % #H1 
@(absurd … (CF s2 (diag_cf s1)))
  [@H1 @diag_s // |@(diag1_not_s1 … H)]
qed.
*)

theorem hierarchy_theorem_left: ∀s1,s2:nat→nat.
   O(s1) ⊆ O(s2) → CF s1 ⊆ CF s2.
#s1 #s2 #HO #f * #i * #Hcode * #c * #a #Hs1_i %{i} % //
cases (sub_O_to_O … HO) -HO #c1 * #b #Hs1s2 
%{(c*c1)} %{(max a b)} #x #lemax 
cases (Hs1_i x ?) [2: @(le_maxl …lemax)]
#y #Hy %{y} @(monotonic_U … Hy) >associative_times
@le_times // @Hs1s2 @(le_maxr … lemax)
qed.

