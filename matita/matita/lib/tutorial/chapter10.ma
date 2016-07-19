(* 
Moves
We now define the move operation, that corresponds to the advancement of the 
state in response to the processing of an input character a. The intuition is 
clear: we have to look at points inside $e$ preceding the given character a,
let the point traverse the character, and broadcast it. All other points must 
be removed.

We can give a particularly elegant definition in terms of the
lifted operators of the previous section:
*)

include "tutorial/chapter9.ma".

let rec move (S: DeqSet) (x:S) (E: pitem S) on E : pre S ≝
 match E with
  [ pz ⇒ 〈 pz S, false 〉
  | pe ⇒ 〈 ϵ, false 〉
  | ps y ⇒ 〈 `y, false 〉
  | pp y ⇒ 〈 `y, x == y 〉
  | po e1 e2 ⇒ (move ? x e1) ⊕ (move ? x e2) 
  | pc e1 e2 ⇒ (move ? x e1) ⊙ (move ? x e2)
  | pk e ⇒ (move ? x e)^⊛ ].
  
lemma move_plus: ∀S:DeqSet.∀x:S.∀i1,i2:pitem S.
  move S x (i1 + i2) = (move ? x i1) ⊕ (move ? x i2).
// qed.

lemma move_cat: ∀S:DeqSet.∀x:S.∀i1,i2:pitem S.
  move S x (i1 · i2) = (move ? x i1) ⊙ (move ? x i2).
// qed.

lemma move_star: ∀S:DeqSet.∀x:S.∀i:pitem S.
  move S x i^* = (move ? x i)^⊛.
// qed.

(*
Example. Let us consider the item                      
  
                               (•a + ϵ)((•b)*•a + •b)b

and the two moves w.r.t. the characters a and b. 
For a, we have two possible positions (all other points gets erased); the innermost 
point stops in front of the final b, while the other one broadcast inside (b^*a + b)b, 
so
 
      move((•a + ϵ)((•b)*•a + •b)b,a) = 〈(a + ϵ)((•b)^*•a + •b)•b, false〉

For b, we have two positions too. The innermost point stops in front of the final b too, 
while the other point reaches the end of b* and must go back through b*a:  
    
      move((•a + ϵ)((•b)*•a + •b)b ,b) = 〈(a +  ϵ)((•b)*•a + b)•b, false〉

*)

definition pmove ≝ λS:DeqSet.λx:S.λe:pre S. move ? x (fst … e).

lemma pmove_def : ∀S:DeqSet.∀x:S.∀i:pitem S.∀b. 
  pmove ? x 〈i,b〉 = move ? x i.
// qed.

lemma eq_to_eq_hd: ∀A.∀l1,l2:list A.∀a,b. 
  a::l1 = b::l2 → a = b.
#A #l1 #l2 #a #b #H destruct //
qed. 

(* Obviously, a move does not change the carrier of the item, as one can easily 
prove by induction on the item. *)

lemma same_kernel: ∀S:DeqSet.∀a:S.∀i:pitem S.
  |fst … (move ? a i)| = |i|.
#S #a #i elim i //
  [#i1 #i2 #H1 #H2 >move_cat >erase_odot //
  |#i1 #i2 #H1 #H2 >move_plus whd in ⊢ (??%%); // 
  ]
qed.

(* Here is our first, major result, stating the correctness of the
move operation. The proof is a simple induction on i. *)

theorem move_ok:
 ∀S:DeqSet.∀a:S.∀i:pitem S.∀w: word S. 
   \sem{move ? a i} w ↔ \sem{i} (a::w).
#S #a #i elim i 
  [normalize /2/
  |normalize /2/
  |normalize /2/
  |normalize #x #w cases (true_or_false (a==x)) #H >H normalize
    [>(\P H) % [* // #bot @False_ind //| #H1 destruct /2/]
    |% [@False_ind |#H1 cases (\Pf H) #H2 @H2 destruct //]
    ]
  |#i1 #i2 #HI1 #HI2 #w >move_cat
   @iff_trans[|@sem_odot] >same_kernel >sem_cat_w
   @iff_trans[||@(iff_or_l … (HI2 w))] @iff_or_r 
   @iff_trans[||@iff_sym @deriv_middot //]
   @cat_ext_l @HI1
  |#i1 #i2 #HI1 #HI2 #w >(sem_plus S i1 i2) >move_plus >sem_plus_w 
   @iff_trans[|@sem_oplus] 
   @iff_trans[|@iff_or_l [|@HI2]| @iff_or_r //]
  |#i1 #HI1 #w >move_star 
   @iff_trans[|@sem_ostar] >same_kernel >sem_star_w 
   @iff_trans[||@iff_sym @deriv_middot //]
   @cat_ext_l @HI1
  ]
qed.
    
(* The move operation is generalized to strings in the obvious way. *)

notation > "x ↦* E" non associative with precedence 60 for @{moves ? $x $E}.

let rec moves (S : DeqSet) w e on w : pre S ≝
 match w with
  [ nil ⇒ e
  | cons x w' ⇒ w' ↦* (move S x (fst … e))]. 

lemma moves_empty: ∀S:DeqSet.∀e:pre S. 
  moves ? [ ] e = e.
// qed.

lemma moves_cons: ∀S:DeqSet.∀a:S.∀w.∀e:pre S. 
  moves ? (a::w)  e = moves ? w (move S a (fst … e)).
// qed.

lemma moves_left : ∀S,a,w,e. 
  moves S (w@(a::[])) e = move S a (fst … (moves S w e)). 
#S #a #w elim w // #x #tl #Hind #e >moves_cons >moves_cons //
qed.

lemma not_epsilon_sem: ∀S:DeqSet.∀a:S.∀w: word S. ∀e:pre S. 
  ((a::w) ∈ e) ↔ ((a::w) ∈ (fst (pitem S) bool e)).
#S #a #w * #i #b cases b normalize 
  [% /2/ * // #H destruct |% normalize /2/]
qed.

lemma same_kernel_moves: ∀S:DeqSet.∀w.∀e:pre S.
  |fst … (moves ? w e)| = |fst … e|.
#S #w elim w //
qed.

theorem decidable_sem: ∀S:DeqSet.∀w: word S. ∀e:pre S. 
   (snd … (moves ? w e) = true) ↔ \sem{e} w.
#S #w elim w 
 [* #i #b >moves_empty cases b % /2/
 |#a #w1 #Hind #e >moves_cons
  @iff_trans [||@iff_sym @not_epsilon_sem]
  @iff_trans [||@move_ok] @Hind
 ]
qed.

(* It is now clear that we can build a DFA D_e for e by taking pre as states, 
and move as transition function; the initial state is •(e) and a state 〈i,b〉 is 
final if and only if b is true. The fact that states in D_e are finite is obvious: 
in fact, their cardinality is at most 2^{n+1} where n is the number of symbols in 
e. This is one of the advantages of pointed regular expressions w.r.t. derivatives, 
whose finite nature only holds after a suitable quotient.

Let us discuss a couple of examples.

Example. 
Below is the DFA associated with the regular expression (ac+bc)*.

DFA for (ac+bc)  

The graphical description of the automaton is the traditional one, with nodes for 
states and labelled arcs for transitions. Unreachable states are not shown.
Final states are emphasized by a double circle: since a state 〈e,b〉 is final if and 
only if b is true, we may just label nodes with the item.
The automaton is not minimal: it is easy to see that the two states corresponding to 
the items (a•c +bc)* and (ac+b•c)* are equivalent (a way to prove it is to observe 
that they define the same language!). In fact, an important property of pres e is that 
each state has a clear semantics, given in terms of the specification e and not of the 
behaviour of the automaton. As a consequence, the construction of the automaton is not 
only direct, but also extremely intuitive and locally verifiable. 

Let us consider a more complex case.

Example. 
Starting form the regular expression (a+ϵ)(b*a + b)b, we obtain the following automaton.

DFA for (a+ϵ)(b*a + b)b 

Remarkably, this DFA is minimal, testifying the small number of states produced by our 
technique (the pair of states 6-8 and 7-9 differ for the fact that 6 and 7 
are final, while 8 and 9 are not). 


Move to pit
. 

We conclude this chapter with a few properties of the move opertions in relation
with the pit state. *)

definition pit_pre ≝ λS.λi.〈blank S (|i|), false〉. 

(* The following "occur" function compute the list of characters occurring in a 
given item i. We first define a special append function that appends two lists 
avoiding repetitions, and prove a few properties of it.
*)

let rec unique_append (S:DeqSet) (l1,l2: list S) on l1 ≝
  match l1 with
  [ nil ⇒ l2
  | cons a tl ⇒ 
     let r ≝ unique_append S tl l2 in
     if memb S a r then r else a::r
  ].
  
lemma memb_unique_append: ∀S,a,l1,l2. 
memb S a (unique_append S l1 l2) = true →
  memb S a l1= true ∨ memb S a l2 = true.
#S #a #l1 elim l1 normalize [#l2 #H %2 //] 
#b #tl #Hind #l2 cases (true_or_false … (a==b)) #Hab >Hab normalize /2/
cases (memb S b (unique_append S tl l2)) normalize 
  [@Hind | >Hab normalize @Hind]   
qed. 

lemma unique_append_elim: ∀S:DeqSet.∀P: S → Prop.∀l1,l2. 
(∀x. memb S x l1 = true → P x) → (∀x. memb S x l2 = true → P x) →
∀x. memb S x (unique_append S l1 l2) = true → P x. 
#S #P #l1 #l2 #Hl1 #Hl2 #x #membx cases (memb_unique_append … membx)
/2/ 
qed.

lemma unique_append_unique: ∀S,l1,l2. uniqueb S l2 = true →
  uniqueb S (unique_append S l1 l2) = true.
#S #l1 elim l1 normalize // #a #tl #Hind #l2 #uniquel2
cases (true_or_false … (memb S a (unique_append S tl l2))) 
#H >H normalize [@Hind //] >H normalize @Hind //
qed.

definition sublist ≝ 
  λS,l1,l2.∀a. memb S a l1 = true → memb S a l2 = true.

lemma memb_exists: ∀S,a,l.memb S a l = true → 
  ∃l1,l2.l=l1@(a::l2).
#S #a #l elim l [normalize #abs @False_ind /2/]
#b #tl #Hind #H cases (orb_true_l … H)
  [#eqba @(ex_intro … (nil S)) @(ex_intro … tl) >(\P eqba) //
  |#mem_tl cases (Hind mem_tl) #l1 * #l2 #eqtl
   @(ex_intro … (b::l1)) @(ex_intro … l2) >eqtl //
  ]
qed.

lemma sublist_length: ∀S,l1,l2. 
 uniqueb S l1 = true → sublist S l1 l2 → |l1| ≤ |l2|.
#S #l1 elim l1 // 
#a #tl #Hind #l2 #unique #sub
cut (∃l3,l4.l2=l3@(a::l4)) [@memb_exists @sub normalize >(\b (refl … a)) //]
* #l3 * #l4 #eql2 >eql2 >length_append normalize 
applyS le_S_S <length_append @Hind [@(andb_true_r … unique)]
>eql2 in sub; #sub #x #membx 
cases (memb_append … (sub x (orb_true_r2 … membx)))
  [#membxl3 @memb_append_l1 //
  |#membxal4 cases (orb_true_l … membxal4)
    [#eqxa @False_ind lapply (andb_true_l … unique)
     <(\P eqxa) >membx normalize /2/ |#membxl4 @memb_append_l2 //
    ]
  ]
qed.

lemma sublist_unique_append_l1: 
  ∀S,l1,l2. sublist S l1 (unique_append S l1 l2).
#S #l1 elim l1 normalize [#l2 #S #abs @False_ind /2/]
#x #tl #Hind #l2 #a 
normalize cases (true_or_false … (a==x)) #eqax >eqax 
[<(\P eqax) cases (true_or_false (memb S a (unique_append S tl l2)))
  [#H >H normalize // | #H >H normalize >(\b (refl … a)) //]
|cases (memb S x (unique_append S tl l2)) normalize 
  [/2/ |>eqax normalize /2/]
]
qed.

lemma sublist_unique_append_l2: 
  ∀S,l1,l2. sublist S l2 (unique_append S l1 l2).
#S #l1 elim l1 [normalize //] #x #tl #Hind normalize 
#l2 #a cases (memb S x (unique_append S tl l2)) normalize
[@Hind | cases (a==x) normalize // @Hind]
qed.

lemma decidable_sublist:∀S,l1,l2. 
  (sublist S l1 l2) ∨ ¬(sublist S l1 l2).
#S #l1 #l2 elim l1 
  [%1 #a normalize in ⊢ (%→?); #abs @False_ind /2/
  |#a #tl * #subtl 
    [cases (true_or_false (memb S a l2)) #memba
      [%1 whd #x #membx cases (orb_true_l … membx)
        [#eqax >(\P eqax) // |@subtl]
      |%2 @(not_to_not … (eqnot_to_noteq … true memba)) #H1 @H1 normalize
       >(\b (refl … a)) //
      ]
    |%2 @(not_to_not … subtl) #H1 #x #H2 @H1 normalize cases (x==a) 
     normalize //
    ] 
  ]
qed.

let rec occur (S: DeqSet) (i: re S) on i ≝  
  match i with
  [ z ⇒ [ ]
  | e ⇒ [ ]
  | s y ⇒ y::[]
  | o e1 e2 ⇒ unique_append ? (occur S e1) (occur S e2) 
  | c e1 e2 ⇒ unique_append ? (occur S e1) (occur S e2) 
  | k e ⇒ occur S e].
  


(* If a symbol a does not occur in i, then move(i,a) gets to the
pit state. *)

lemma not_occur_to_pit: ∀S,a.∀i:pitem S. memb S a (occur S (|i|)) ≠ true →
  move S a i  = pit_pre S i.
#S #a #i elim i //
  [#x normalize cases (a==x) normalize // #H @False_ind /2/
  |#i1 #i2 #Hind1 #Hind2 #H >move_cat 
   >Hind1 [2:@(not_to_not … H) #H1 @sublist_unique_append_l1 //]
   >Hind2 [2:@(not_to_not … H) #H1 @sublist_unique_append_l2 //] //
  |#i1 #i2 #Hind1 #Hind2 #H >move_plus 
   >Hind1 [2:@(not_to_not … H) #H1 @sublist_unique_append_l1 //]
   >Hind2 [2:@(not_to_not … H) #H1 @sublist_unique_append_l2 //] //
  |#i #Hind #H >move_star >Hind // 
  ]
qed.

(* We cannot escape form the pit state. *)

lemma move_pit: ∀S,a,i. move S a (fst ?? (pit_pre S i)) = pit_pre S i.
#S #a #i elim i //
  [#i1 #i2 #Hind1 #Hind2 >move_cat >Hind1 >Hind2 // 
  |#i1 #i2 #Hind1 #Hind2 >move_plus >Hind1 >Hind2 // 
  |#i #Hind >move_star >Hind //
  ]
qed. 

lemma moves_pit: ∀S,w,i. moves S w (pit_pre S i) = pit_pre S i.
#S #w #i elim w // #a #w1 #H normalize >move_pit @H 
qed.  
 
(* If any character in w does not occur in i, then moves(i,w) gets
to the pit state. *)

lemma to_pit: ∀S,w,e. ¬ sublist S w (occur S (|fst ?? e|)) →
 moves S w e = pit_pre S (fst ?? e).
#S #w elim w
  [#e * #H @False_ind @H normalize #a #abs @False_ind /2/
  |#a #tl #Hind #e #H cases (true_or_false (memb S a (occur S (|fst ?? e|))))
    [#Htrue >moves_cons whd in ⊢ (???%); <(same_kernel … a) 
     @Hind >same_kernel @(not_to_not … H) #H1 #b #memb cases (orb_true_l … memb)
      [#H2 >(\P H2) // |#H2 @H1 //]
    |#Hfalse >moves_cons >not_occur_to_pit // >Hfalse /2/ 
    ]
  ]
qed.