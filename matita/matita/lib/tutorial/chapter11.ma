(* 
Regular Expressions Equivalence
*)

include "tutorial/chapter10.ma".

(* We say that two pres 〈i_1,b_1〉 and 〈i_1,b_1〉 are {\em cofinal} if and 
only if b_1 = b_2. *)

definition cofinal ≝ λS.λp:(pre S)×(pre S). 
  snd ?? (fst ?? p) = snd ?? (snd ?? p).

(* As a corollary of decidable_sem, we have that two expressions
e1 and e2 are equivalent iff for any word w the states reachable 
through w are cofinal. *)

theorem equiv_sem: ∀S:DeqSet.∀e1,e2:pre S. 
  \sem{e1} ≐ \sem{e2} ↔ ∀w.cofinal ? 〈moves ? w e1,moves ? w e2〉.
#S #e1 #e2 % 
[#same_sem #w 
  cut (∀b1,b2. iff (b1 = true) (b2 = true) → (b1 = b2)) 
    [* * // * #H1 #H2 [@sym_eq @H1 //| @H2 //]]
  #Hcut @Hcut @iff_trans [|@decidable_sem] 
  @iff_trans [|@same_sem] @iff_sym @decidable_sem
|#H #w1 @iff_trans [||@decidable_sem] <H @iff_sym @decidable_sem]
qed.

(* This does not directly imply decidability: we have no bound over the
length of w; moreover, so far, we made no assumption over the cardinality 
of S. Instead of requiring S to be finite, we may restrict the analysis
to characters occurring in the given pres. *)

definition occ ≝ λS.λe1,e2:pre S. 
  unique_append ? (occur S (|fst ?? e1|)) (occur S (|fst ?? e2|)).

lemma occ_enough: ∀S.∀e1,e2:pre S.
(∀w.(sublist S w (occ S e1 e2))→ cofinal ? 〈moves ? w e1,moves ? w e2〉)
 →∀w.cofinal ? 〈moves ? w e1,moves ? w e2〉.
#S #e1 #e2 #H #w
cases (decidable_sublist S w (occ S e1 e2)) [@H] -H #H
 >to_pit [2: @(not_to_not … H) #H1 #a #memba @sublist_unique_append_l1 @H1 //]
 >to_pit [2: @(not_to_not … H) #H1 #a #memba  @sublist_unique_append_l2 @H1 //]
 //
qed.

(* The following is a stronger version of equiv_sem, relative to characters
occurring the given regular expressions. *)

lemma equiv_sem_occ: ∀S.∀e1,e2:pre S.
(∀w.(sublist S w (occ S e1 e2))→ cofinal ? 〈moves ? w e1,moves ? w e2〉)
→ \sem{e1} ≐ \sem{e2}.
#S #e1 #e2 #H @(proj2 … (equiv_sem …)) @occ_enough #w @H 
qed.

(* 
Bisimulations


We say that a list of pairs of pres is a bisimulation if it is closed
w.r.t. moves, and all its members are cofinal.
*)

definition sons ≝ λS:DeqSet.λl:list S.λp:(pre S)×(pre S). 
 map ?? (λa.〈move S a (fst … (fst … p)),move S a (fst … (snd … p))〉) l.

lemma memb_sons: ∀S,l.∀p,q:(pre S)×(pre S). memb ? p (sons ? l q) = true →
  ∃a.(move ? a (fst … (fst … q)) = fst … p ∧
      move ? a (fst … (snd … q)) = snd … p).
#S #l elim l [#p #q normalize in ⊢ (%→?); #abs @False_ind /2/] 
#a #tl #Hind #p #q #H cases (orb_true_l … H) -H
  [#H @(ex_intro … a) >(\P H) /2/ |#H @Hind @H]
qed.

definition is_bisim ≝ λS:DeqSet.λl:list ?.λalpha:list S.
  ∀p:(pre S)×(pre S). memb ? p l = true → cofinal ? p ∧ (sublist ? (sons ? alpha p) l).

(* We define an elimination principle for lists working on the tail, that we
be used in the sequel *)

lemma list_elim_left: ∀S.∀P:list S → Prop. P (nil S) →
(∀a.∀tl.P tl → P (tl@[a])) → ∀l. P l.
#S #P #Pnil #Pstep #l <(reverse_reverse … l) 
generalize in match (reverse S l); #l elim l //
#a #tl #H >reverse_cons @Pstep //
qed.

(* Using lemma equiv_sem_occ it is easy to prove the following result: *)

lemma bisim_to_sem: ∀S:DeqSet.∀l:list ?.∀e1,e2: pre S. 
  is_bisim S l (occ S e1 e2) → memb ?〈e1,e2〉 l = true → \sem{e1} ≐ \sem{e2}.
#S #l #e1 #e2 #Hbisim #Hmemb @equiv_sem_occ 
#w #Hsub @(proj1 … (Hbisim 〈moves S w e1,moves S w e2〉 ?))
lapply Hsub @(list_elim_left … w) [//]
#a #w1 #Hind #Hsub >moves_left >moves_left @(proj2 …(Hbisim …(Hind ?)))
  [#x #Hx @Hsub @memb_append_l1 //
  |cut (memb S a (occ S e1 e2) = true) 
    [@Hsub @memb_append_l2 normalize >(\b (refl … a)) //] #occa 
   @(memb_map … occa)
  ]
qed.

(* This is already an interesting result: checking if l is a bisimulation 
is decidable, hence we could generate l with some untrusted piece of code 
and then run a (boolean version of) is_bisim to check that it is actually 
a bisimulation. 
However, in order to prove that equivalence of regular expressions
is decidable we must prove that we can always effectively build such a list 
(or find a counterexample).
The idea is that the list we are interested in is just the set of 
all pair of pres reachable from the initial pair via some
sequence of moves. 

The algorithm for computing reachable nodes in graph is a very 
traditional one. We split nodes in two disjoint lists: a list of 
visited nodes and a frontier, composed by all nodes connected
to a node in visited but not visited already. At each step we select a node 
a from the frontier, compute its sons, add a to the set of 
visited nodes and the (not already visited) sons to the frontier. 

Instead of fist computing reachable nodes and then performing the 
bisimilarity test we can directly integrate it in the algorithm:
the set of visited nodes is closed by construction w.r.t. reachability,
so we have just to check cofinality for any node we add to visited.

Here is the extremely simple algorithm: *)

let rec bisim S l n (frontier,visited: list ?) on n ≝
  match n with 
  [ O ⇒ 〈false,visited〉 (* assert false *)
  | S m ⇒ 
    match frontier with
    [ nil ⇒ 〈true,visited〉
    | cons hd tl ⇒
      if beqb (snd … (fst … hd)) (snd … (snd … hd)) then
        bisim S l m (unique_append ? (filter ? (λx.notb (memb ? x (hd::visited))) 
        (sons S l hd)) tl) (hd::visited)
      else 〈false,visited〉
    ]
  ].

(* The integer n is an upper bound to the number of recursive call, 
equal to the dimension of the graph. It returns a pair composed
by a boolean and a the set of visited nodes; the boolean is true
if and only if all visited nodes are cofinal. 

The following results explicitly state the behaviour of bisim is the general
case and in some relevant instances *)

lemma unfold_bisim: ∀S,l,n.∀frontier,visited: list ?.
  bisim S l n frontier visited =
  match n with 
  [ O ⇒ 〈false,visited〉 (* assert false *)
  | S m ⇒ 
    match frontier with
    [ nil ⇒ 〈true,visited〉
    | cons hd tl ⇒
      if beqb (snd … (fst … hd)) (snd … (snd … hd)) then
        bisim S l m (unique_append ? (filter ? (λx.notb(memb ? x (hd::visited))) 
          (sons S l hd)) tl) (hd::visited)
      else 〈false,visited〉
    ]
  ].
#S #l #n cases n // qed.

lemma bisim_never: ∀S,l.∀frontier,visited: list ?.
  bisim S l O frontier visited = 〈false,visited〉.
#frontier #visited >unfold_bisim // 
qed.

lemma bisim_end: ∀Sig,l,m.∀visited: list ?.
  bisim Sig l (S m) [] visited = 〈true,visited〉.
#n #visisted >unfold_bisim // 
qed.

lemma bisim_step_true: ∀Sig,l,m.∀p.∀frontier,visited: list ?.
beqb (snd … (fst … p)) (snd … (snd … p)) = true →
  bisim Sig l (S m) (p::frontier) visited = 
  bisim Sig l m (unique_append ? (filter ? (λx.notb(memb ? x (p::visited))) 
    (sons Sig l p)) frontier) (p::visited).
#Sig #l #m #p #frontier #visited #test >unfold_bisim whd in ⊢ (??%?);  >test // 
qed.

lemma bisim_step_false: ∀Sig,l,m.∀p.∀frontier,visited: list ?.
beqb (snd … (fst ?? p)) (snd ?? (snd ?? p)) = false →
  bisim Sig l (S m) (p::frontier) visited = 〈false,visited〉.
#Sig #l #m #p #frontier #visited #test >unfold_bisim whd in ⊢ (??%?); >test // 
qed.

(* In order to prove termination of bisim we must be able to effectively 
enumerate all possible pres: *)
 
(* lemma notb_eq_true_l: ∀b. notb b = true → b = false.
#b cases b normalize //
qed. *)

let rec pitem_enum S (i:re S) on i ≝
  match i with
  [ z ⇒ (pz S)::[]
  | e ⇒ (pe S)::[]
  | s y ⇒ (ps S y)::(pp S y)::[]
  | o i1 i2 ⇒ compose ??? (po S) (pitem_enum S i1) (pitem_enum S i2)
  | c i1 i2 ⇒ compose ??? (pc S) (pitem_enum S i1) (pitem_enum S i2)
  | k i ⇒ map ?? (pk S) (pitem_enum S i)
  ].
  
lemma pitem_enum_complete : ∀S.∀i:pitem S.
  memb (DeqItem S) i (pitem_enum S (|i|)) = true.
#S #i elim i 
  [1,2://
  |3,4:#c normalize >(\b (refl … c)) //
  |5,6:#i1 #i2 #Hind1 #Hind2 @(memb_compose (DeqItem S) (DeqItem S)) //
  |#i #Hind @(memb_map (DeqItem S)) //
  ]
qed.

definition pre_enum ≝ λS.λi:re S.
  compose ??? (λi,b.〈i,b〉) ( pitem_enum S i) (true::false::[]).
  
lemma pre_enum_complete : ∀S.∀e:pre S.
  memb ? e (pre_enum S (|fst ?? e|)) = true.
#S * #i #b @(memb_compose (DeqItem S) DeqBool ? (λi,b.〈i,b〉))
// cases b normalize //
qed.
 
definition space_enum ≝ λS.λi1,i2: re S.
  compose ??? (λe1,e2.〈e1,e2〉) ( pre_enum S i1) (pre_enum S i2).

lemma space_enum_complete : ∀S.∀e1,e2: pre S.
  memb ? 〈e1,e2〉 ( space_enum S (|fst ?? e1|) (|fst ?? e2|)) = true.
#S #e1 #e2 @(memb_compose ?? (DeqProd (DeqProd ??) (DeqProd ??)) (λi,b.〈i,b〉))
// qed. 

definition all_reachable ≝ λS.λe1,e2:pre S.
λl: list (DeqProd (DeqProd ??) (DeqProd ??)).
uniqueb ? l = true ∧ 
  ∀p. memb ? p l = true → 
    ∃w.(moves S w e1 = fst ?? p) ∧ (moves S w e2 = snd ?? p).
    
definition disjoint ≝ λS:DeqSet.λl1,l2.
  ∀p:S. memb S p l1 = true →  memb S p l2 = false.
        
(* We are ready to prove that bisim is correct; we use the invariant 
that at each call of bisim the two lists visited and frontier only contain 
nodes reachable from 〈e_1,e_2〉, hence it is absurd to suppose to meet a pair 
which is not cofinal. *)

(* we first prove a few auxiliary results *)
lemma memb_filter_memb: ∀S,f,a,l. 
  memb S a (filter S f l) = true → memb S a l = true.
#S #f #a #l elim l [normalize //] #b #tl #Hind normalize (cases (f b)) normalize 
cases (a==b) normalize // @Hind
qed.
  
lemma filter_true: ∀S,f,a,l. 
  memb S a (filter S f l) = true → f a = true.
#S #f #a #l elim l [normalize #H @False_ind /2/] #b #tl #Hind 
cases (true_or_false (f b)) #H normalize >H normalize [2:@Hind]
cases (true_or_false (a==b)) #eqab [#_ >(\P eqab) // | >eqab normalize @Hind]
qed. 

lemma memb_filter_l: ∀S,f,x,l. (f x = true) → memb S x l = true →
memb S x (filter ? f l) = true.
#S #f #x #l #fx elim l normalize //
#b #tl #Hind cases (true_or_false (x==b)) #eqxb
  [<(\P eqxb) >(\b (refl … x)) >fx normalize >(\b (refl … x)) normalize //
  |>eqxb cases (f b) normalize [>eqxb normalize @Hind| @Hind]
  ]
qed. 

lemma bisim_correct: ∀S.∀e1,e2:pre S.\sem{e1} ≐ \sem{e2} → 
 ∀l,n.∀frontier,visited:list ((pre S)×(pre S)).
 |space_enum S (|fst ?? e1|) (|fst ?? e2|)| < n + |visited|→
 all_reachable S e1 e2 visited →  
 all_reachable S e1 e2 frontier →
 disjoint ? frontier visited →
 fst ?? (bisim S l n frontier visited) = true.
#Sig #e1 #e2 #same #l #n elim n 
  [#frontier #visited #abs * #unique #H @False_ind @(absurd … abs)
   @le_to_not_lt @sublist_length // * #e11 #e21 #membp 
   cut ((|fst ?? e11| = |fst ?? e1|) ∧ (|fst ?? e21| = |fst ?? e2|))
   [|* #H1 #H2 <H1 <H2 @space_enum_complete]
   cases (H … membp) #w * normalize #we1 #we2 <we1 <we2 % >same_kernel_moves //    
  |#m #HI * [#visited #vinv #finv >bisim_end //]
   #p #front_tl #visited #Hn * #u_visited #r_visited * #u_frontier #r_frontier 
   #disjoint
   cut (∃w.(moves ? w e1 = fst ?? p) ∧ (moves ? w e2 = snd ?? p)) 
    [@(r_frontier … (memb_hd … ))] #rp
   cut (beqb (snd ?? (fst ?? p)) (snd ?? (snd ?? p)) = true)
    [cases rp #w * #fstp #sndp <fstp <sndp @(\b ?) 
     @(proj1 … (equiv_sem … )) @same] #ptest 
   >(bisim_step_true … ptest) @HI -HI 
     [<plus_n_Sm //
     |% [whd in ⊢ (??%?); >(disjoint … (memb_hd …)) whd in ⊢ (??%?); //
        |#p1 #H (cases (orb_true_l … H)) [#eqp >(\P eqp) // |@r_visited]
        ]
     |whd % [@unique_append_unique @(andb_true_r … u_frontier)]
      @unique_append_elim #q #H
       [cases (memb_sons … (memb_filter_memb … H)) -H
       
        #a * #m1 #m2 cases rp #w1 * #mw1 #mw2 @(ex_intro … (w1@(a::[])))
        >moves_left >moves_left >mw1 >mw2 >m1 >m2 % // 
       |@r_frontier @memb_cons //
       ]
     |@unique_append_elim #q #H
       [@injective_notb @(filter_true … H)
       |cut ((q==p) = false) 
         [|#Hpq whd in ⊢ (??%?); >Hpq @disjoint @memb_cons //]
        cases (andb_true … u_frontier) #notp #_ @(\bf ?) 
        @(not_to_not … not_eq_true_false) #eqqp <notp <eqqp >H //
       ]
     ]
   ]  
qed.  

(* For completeness, we use the invariant that all the nodes in visited are cofinal, 
and the sons of visited are either in visited or in the frontier; since
at the end frontier is empty, visited is hence a bisimulation. *)

definition all_true ≝ λS.λl.∀p:(pre S) × (pre S). memb ? p l = true → 
  (beqb (snd ?? (fst ?? p)) (snd ?? (snd ?? p)) = true).

definition sub_sons ≝ λS,l,l1,l2.∀x:(pre S) × (pre S). 
memb ? x l1 = true → sublist ? (sons ? l x) l2. 

lemma bisim_complete: 
 ∀S,l,n.∀frontier,visited,visited_res:list ?.
 all_true S visited →
 sub_sons S l visited (frontier@visited) →
 bisim S l n frontier visited = 〈true,visited_res〉 →
 is_bisim S visited_res l ∧ sublist ? (frontier@visited) visited_res. 
#S #l #n elim n
  [#fron #vis #vis_res #_ #_ >bisim_never #H destruct
  |#m #Hind * 
    [(* case empty frontier *)
     -Hind #vis #vis_res #allv #H normalize in  ⊢ (%→?);
     #H1 destruct % #p 
      [#membp % [@(\P ?) @allv //| @H //]|#H1 @H1]
    |#hd cases (true_or_false (beqb (snd ?? (fst ?? hd)) (snd ?? (snd ?? hd))))
      [|(* case head of the frontier is non ok (absurd) *)
       #H #tl #vis #vis_res #allv >(bisim_step_false … H) #_ #H1 destruct]
     (* frontier = hd:: tl and hd is ok *)
     #H #tl #visited #visited_res #allv >(bisim_step_true … H)
     (* new_visited = hd::visited are all ok *)
     cut (all_true S (hd::visited)) 
      [#p #H1 cases (orb_true_l … H1) [#eqp >(\P eqp) @H |@allv]]
     (* we now exploit the induction hypothesis *)
     #allh #subH #bisim cases (Hind … allh … bisim) -bisim -Hind
      [#H1 #H2 % // #p #membp @H2 -H2 cases (memb_append … membp) -membp #membp
        [cases (orb_true_l … membp) -membp #membp
          [@memb_append_l2 >(\P membp) @memb_hd
          |@memb_append_l1 @sublist_unique_append_l2 // 
          ]
        |@memb_append_l2 @memb_cons //
        ] 
      |(* the only thing left to prove is the sub_sons invariant *)  
     #x #membx cases (orb_true_l … membx)
      [(* case x = hd *) 
       #eqhdx <(\P eqhdx) #xa #membxa
       (* xa is a son of x; we must distinguish the case xa 
        was already visited form the case xa is new *)
       cases (true_or_false … (memb ? xa (x::visited)))
        [(* xa visited - trivial *) #membxa @memb_append_l2 //
        |(* xa new *) #membxa @memb_append_l1 @sublist_unique_append_l1 
         @memb_filter_l [>membxa //|//]
        ]
      |(* case x in visited *)
       #H1 #xa #membxa cases (memb_append … (subH x … H1 … membxa))  
        [#H2 (cases (orb_true_l … H2)) 
          [#H3 @memb_append_l2 <(\P H3) @memb_hd
          |#H3 @memb_append_l1 @sublist_unique_append_l2 @H3
          ]
        |#H2 @memb_append_l2 @memb_cons @H2
        ]
      ]
    ]
  ]
qed.

(* We can now give the definition of the equivalence algorithm, and
prove that two expressions are equivalente if and only if they define
the same language. *)

definition equiv ≝ λSig.λre1,re2:re Sig. 
  let e1 ≝ •(blank ? re1) in
  let e2 ≝ •(blank ? re2) in
  let n ≝ S (length ? (space_enum Sig (|fst ?? e1|) (|fst ?? e2|))) in
  let sig ≝ (occ Sig e1 e2) in
  (bisim ? sig n (〈e1,e2〉::[]) []).

theorem euqiv_sem : ∀Sig.∀e1,e2:re Sig.
   fst ?? (equiv ? e1 e2) = true ↔ \sem{e1} ≐ \sem{e2}.
#Sig #re1 #re2 %
  [#H @eqP_trans [|@eqP_sym @re_embedding] @eqP_trans [||@re_embedding]
   cut (equiv ? re1 re2 = 〈true,snd ?? (equiv ? re1 re2)〉)
     [<H //] #Hcut
   cases (bisim_complete … Hcut) 
     [2,3: #p whd in ⊢ ((??%?)→?); #abs @False_ind /2/] 
   #Hbisim #Hsub @(bisim_to_sem … Hbisim) 
   @Hsub @memb_hd
  |#H @(bisim_correct ? (•(blank ? re1)) (•(blank ? re2))) 
    [@eqP_trans [|@re_embedding] @eqP_trans [|@H] @eqP_sym @re_embedding
    |// 
    |% // #p whd in ⊢ ((??%?)→?); #abs @False_ind /2/  
    |% // #p #H >(memb_single … H) @(ex_intro … ϵ) /2/
    |#p #_ normalize //
    ]
  ]
qed.

definition eqbnat ≝ λn,m:nat. eqb n m.

lemma eqbnat_true : ∀n,m. eqbnat n m = true ↔ n = m.
#n #m % [@eqb_true_to_eq | @eq_to_eqb_true]
qed.

definition DeqNat ≝ mk_DeqSet nat eqb eqbnat_true.

definition a ≝ s DeqNat O.
definition b ≝ s DeqNat (S O).
definition c ≝ s DeqNat (S (S O)).

definition exp1 ≝ ((a·b)^*·a).
definition exp2 ≝ a·(b·a)^*.
definition exp4 ≝ (b·a)^*.

definition exp6 ≝ a·(a ·a ·b^* + b^* ).
definition exp7 ≝ a · a^* · b^*.

definition exp8 ≝ a·a·a·a·a·a·a·a·(a^* ).
definition exp9 ≝ (a·a·a + a·a·a·a·a)^*.

example ex1 : fst ?? (equiv ? (exp8+exp9) exp9) = true.
normalize // qed.