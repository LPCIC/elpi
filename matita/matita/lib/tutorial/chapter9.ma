(*
Broadcasting points

Intuitively, a regular expression e must be understood as a pointed expression with a single 
point in front of it. Since however we only allow points before symbols, we must broadcast 
this initial point inside e traversing all nullable subexpressions, that essentially corresponds 
to the ϵ-closure operation on automata. We use the notation •(_) to denote such an operation;
its definition is the expected one: let us start discussing an example.

Example
Let us broadcast a point inside (a + ϵ)(b*a + b)b. We start working in parallel on the 
first occurrence of a (where the point stops), and on ϵ that gets traversed. We have hence 
reached the end of a + ϵ and we must pursue broadcasting inside (b*a + b)b. Again, we work in 
parallel on the two additive subterms b^*a and b; the first point is allowed to both enter the 
star, and to traverse it, stopping in front of a; the second point just stops in front of b. 
No point reached that end of b^*a + b hence no further propagation is possible. In conclusion: 
               •((a + ϵ)(b^*a + b)b) = 〈(•a + ϵ)((•b)^*•a + •b)b, false〉
*)

include "tutorial/chapter8.ma".

(* Broadcasting a point inside an item generates a pre, since the point could possibly reach 
the end of the expression. 
Broadcasting inside a i1+i2 amounts to broadcast in parallel inside i1 and i2.
If we define
                 〈i1,b1〉 ⊕ 〈i2,b2〉 = 〈i1 + i2, b1∨ b2〉
then, we just have •(i1+i2) = •(i1)⊕ •(i2).
*)

definition lo ≝ λS:DeqSet.λa,b:pre S.〈fst … a + fst \dots b,snd \dots a ∨ snd \dots b〉.
notation "a ⊕ b" left associative with precedence 60 for @{'oplus $a $b}.
interpretation "oplus" 'oplus a b = (lo ? a b).

lemma lo_def: ∀S.∀i1,i2:pitem S.∀b1,b2. 〈i1,b1〉⊕〈i2,b2〉=〈i1+i2,b1∨b2〉.
// qed.

(*
Concatenation is a bit more complex. In order to broadcast a point inside i1 · i2 
we should start broadcasting it inside i1 and then proceed into i2 if and only if a 
point reached the end of i1. This suggests to define •(i1 · i2) as •(i1) ▹ i2, where 
e ▹ i is a general operation of concatenation between a pre and an item, defined by 
cases on the boolean in e: 

       〈i1,true〉 ▹ i2  = i1 ◃ •(i_2)
       〈i1,false〉 ▹ i2 = i1 · i2
In turn, ◃ says how to concatenate an item with a pre, that is however extremely simple:
        i1 ◃ 〈i1,b〉  = 〈i_1 · i2, b〉
Let us come to the formalized definitions:
*)

definition pre_concat_r ≝ λS:DeqSet.λi:pitem S.λe:pre S.
  match e with [ pair i1 b ⇒ 〈i · i1, b〉].
 
notation "i ◃ e" left associative with precedence 60 for @{'lhd $i $e}.
interpretation "pre_concat_r" 'lhd i e = (pre_concat_r ? i e).

lemma eq_to_ex_eq: ∀S.∀A,B:word S → Prop. 
  A = B → A ≐ B. 
#S #A #B #H >H #x % // qed.

(* The behaoviour of ◃ is summarized by the following, easy lemma: *)

lemma sem_pre_concat_r : ∀S,i.∀e:pre S.
  \sem{i ◃ e} \doteq \sem{i} · \sem{|fst \dots e|} ∪ \sem{e}.
#S #i * #i1 #b1 cases b1 [2: @eq_to_ex_eq //] 
>sem_pre_true >sem_cat >sem_pre_true whd in match (fst ???); // 
qed.
 
(* The definition of $•(-)$ (eclose) and ▹ (pre_concat_l) are mutually recursive.
In this situation, a viable alternative that is usually simpler to reason about, 
is to abstract one of the two functions with respect to the other. In particular
we abstract pre_concat_l with respect to an input bcast function from items to
pres. *)

definition pre_concat_l ≝ λS:DeqSet.λbcast:∀S:DeqSet.pitem S → pre S.λe1:pre S.λi2:pitem S.
  match e1 with 
  [ pair i1 b1 ⇒ match b1 with 
    [ true ⇒ (i1 ◃ (bcast ? i2)) 
    | false ⇒ 〈i1 · i2,false〉
    ]
  ].

notation "a ▹ b" left associative with precedence 60 for @{'tril eclose $a $b}.
interpretation "item-pre concat" 'tril op a b = (pre_concat_l ? op a b).

(* We are ready to give the formal definition of the broadcasting operation. *)

notation "•" non associative with precedence 60 for @{eclose ?}.

let rec eclose (S: DeqSet) (i: pitem S) on i : pre S ≝
 match i with
  [ pz ⇒ 〈 pz ?, false 〉
  | pe ⇒ 〈 ϵ,  true 〉
  | ps x ⇒ 〈 `.x, false 〉
  | pp x ⇒ 〈 `.x, false 〉
  | po i1 i2 ⇒ •i1 ⊕ •i2
  | pc i1 i2 ⇒ •i1 ▹ i2
  | pk i ⇒ 〈(fst \dots (•i))^*,true〉].
  
notation "• x" non associative with precedence 60 for @{'eclose $x}.
interpretation "eclose" 'eclose x = (eclose ? x).

(* Here are a few simple properties of ▹ and •(-) *)

lemma pcl_true : ∀S.∀i1,i2:pitem S.
  〈i1,true〉 ▹ i2 = i1 ◃ (•i2).
// qed.

lemma pcl_true_bis : ∀S.∀i1,i2:pitem S.
  〈i1,true〉 ▹ i2 = 〈i1 · fst \dots (•i2), snd \dots (•i2)〉.
#S #i1 #i2 normalize cases (•i2) // qed.

lemma pcl_false: ∀S.∀i1,i2:pitem S.
  〈i1,false〉 ▹  i2  = 〈i1 · i2, false〉.
// qed.

lemma eclose_plus: ∀S:DeqSet.∀i1,i2:pitem S.
  •(i1 + i2) = •i1 ⊕ •i2.
// qed.

lemma eclose_dot: ∀S:DeqSet.∀i1,i2:pitem S.
  •(i1 · i2) = •i1 ▹ i2.
// qed.

lemma eclose_star: ∀S:DeqSet.∀i:pitem S.
  •i^* = 〈(fst \dots(•i))^*,true〉.
// qed.

(* The definition of •(-) (eclose) can then be lifted from items to pres
in the obvious way. *)

definition lift ≝ λS.λf:pitem S →pre S.λe:pre S. 
  match e with 
  [ pair i b ⇒ 〈fst \dots (f i), snd \dots (f i) ∨ b〉].
  
definition preclose ≝ λS. lift S (eclose S). 
interpretation "preclose" 'eclose x = (preclose ? x).

(* Obviously, broadcasting does not change the carrier of the item,
as it is easily proved by structural induction. *)

lemma erase_bull : ∀S.∀i:pitem S. |fst \dots (•i)| = |i|.
#S #i elim i // 
  [ #i1 #i2 #IH1 #IH2 >erase_dot <IH1 >eclose_dot
    cases (•i1) #i11 #b1 cases b1 // <IH2 >pcl_true_bis //
  | #i1 #i2 #IH1 #IH2 >eclose_plus >(erase_plus … i1) <IH1 <IH2
    cases (•i1) #i11 #b1 cases (•i2) #i21 #b2 //  
  | #i #IH >eclose_star >(erase_star … i) <IH cases (•i) //
  ]
qed.

(* We are now ready to state the main semantic properties of ⊕, ◃ and •(-):

sem_oplus:     \sem{e1 ⊕ e2} =1 \sem{e1} ∪ \sem{e2} 
sem_pcl:       \sem{e1 ▹ i2} =1  \sem{e1} · \sem{|i2|} ∪ \sem{i2}
sem_bullet     \sem{•i} =1 \sem{i} ∪ \sem{|i|}

The proof of sem_oplus is straightforward. *)

lemma sem_oplus: ∀S:DeqSet.∀e1,e2:pre S.
  \sem{e1 ⊕ e2} ≐ \sem{e1} ∪ \sem{e2}. 
#S * #i1 #b1 * #i2 #b2 #w %
  [cases b1 cases b2 normalize /2/ * /3/ * /3/
  |cases b1 cases b2 normalize /2/ * /3/ * /3/
  ]
qed.

(* For the others, we proceed as follow: we first prove the following 
auxiliary lemma, that assumes sem_bullet:

sem_pcl_aux: 
   \sem{•i2} =1  \sem{i2} ∪ \sem{|i2|} →
   \sem{e1 ▹ i2} =1  \sem{e1} · \sem{|i2|} ∪ \sem{i2}.

Then, using the previous result, we prove sem_bullet by induction 
on i. Finally, sem_pcl_aux and sem_bullet give sem_pcl. *)

lemma LcatE : ∀S.∀e1,e2:pitem S.
  \sem{e1 · e2} = \sem{e1} · \sem{|e2|} ∪ \sem{e2}. 
// qed.

lemma sem_pcl_aux : ∀S.∀e1:pre S.∀i2:pitem S.
   \sem{•i2} ≐ \sem{i2} ∪ \sem{|i2|} →
   \sem{e1 ▹ i2} ≐ \sem{e1} · \sem{|i2|} ∪ \sem{i2}.
#S * #i1 #b1 #i2 cases b1
  [2:#th >pcl_false >sem_pre_false >sem_pre_false >sem_cat /2/
  |#H >pcl_true >sem_pre_true @(eqP_trans … (sem_pre_concat_r …))
   >erase_bull @eqP_trans [|@(eqP_union_l … H)]
    @eqP_trans [|@eqP_union_l[|@union_comm ]]
    @eqP_trans [|@eqP_sym @union_assoc ] /3/ 
  ]
qed.
  
lemma minus_eps_pre_aux: ∀S.∀e:pre S.∀i:pitem S.∀A. 
 \sem{e} ≐ \sem{i} ∪ A → \sem{fst \dots e} ≐ \sem{i} ∪ (A - {[ ]}).
#S #e #i #A #seme
@eqP_trans [|@minus_eps_pre]
@eqP_trans [||@eqP_union_r [|@eqP_sym @minus_eps_item]]
@eqP_trans [||@distribute_substract] 
@eqP_substract_r //
qed.

theorem sem_bull: ∀S:DeqSet. ∀i:pitem S.  \sem{•i} ≐ \sem{i} ∪ \sem{|i|}.
#S #e elim e 
  [#w normalize % [/2/ | * //]
  |/2/ 
  |#x normalize #w % [ /2/ | * [@False_ind | //]]
  |#x normalize #w % [ /2/ | * // ] 
  |#i1 #i2 #IH1 #IH2 >eclose_dot
   @eqP_trans [|@sem_pcl_aux //] >sem_cat 
   @eqP_trans
     [|@eqP_union_r
       [|@eqP_trans [|@(cat_ext_l … IH1)] @distr_cat_r]]
   @eqP_trans [|@union_assoc]
   @eqP_trans [||@eqP_sym @union_assoc]
   @eqP_union_l //
  |#i1 #i2 #IH1 #IH2 >eclose_plus
   @eqP_trans [|@sem_oplus] >sem_plus >erase_plus 
   @eqP_trans [|@(eqP_union_l … IH2)]
   @eqP_trans [|@eqP_sym @union_assoc]
   @eqP_trans [||@union_assoc] @eqP_union_r
   @eqP_trans [||@eqP_sym @union_assoc]
   @eqP_trans [||@eqP_union_l [|@union_comm]]
   @eqP_trans [||@union_assoc] /2/
  |#i #H >sem_pre_true >sem_star >erase_bull >sem_star
   @eqP_trans [|@eqP_union_r [|@cat_ext_l [|@minus_eps_pre_aux //]]]
   @eqP_trans [|@eqP_union_r [|@distr_cat_r]]
   @eqP_trans [|@union_assoc] @eqP_union_l >erase_star 
   @eqP_sym @star_fix_eps 
  ]
qed.

(*
Blank item
 

As a corollary of theorem sem_bullet, given a regular expression e, we can easily 
find an item with the same semantics of $e$: it is enough to get an item (blank e) 
having e as carrier and no point, and then broadcast a point in it. The semantics of
(blank e) is obviously the empty language: from the point of view of the automaton,
it corresponds with the pit state. *)

let rec blank (S: DeqSet) (i: re S) on i :pitem S ≝
 match i with
  [ z ⇒ pz ?
  | e ⇒ ϵ
  | s y ⇒ `y
  | o e1 e2 ⇒ (blank S e1) + (blank S e2) 
  | c e1 e2 ⇒ (blank S e1) · (blank S e2)
  | k e ⇒ (blank S e)^* ].
  
lemma forget_blank: ∀S.∀e:re S.|blank S e| = e.
#S #e elim e normalize //
qed.

lemma sem_blank: ∀S.∀e:re S.\sem{blank S e} ≐ ∅.
#S #e elim e 
  [1,2:@eq_to_ex_eq // 
  |#s @eq_to_ex_eq //
  |#e1 #e2 #Hind1 #Hind2 >sem_cat 
   @eqP_trans [||@(union_empty_r … ∅)] 
   @eqP_trans [|@eqP_union_l[|@Hind2]] @eqP_union_r
   @eqP_trans [||@(cat_empty_l … ?)] @cat_ext_l @Hind1
  |#e1 #e2 #Hind1 #Hind2 >sem_plus 
   @eqP_trans [||@(union_empty_r … ∅)] 
   @eqP_trans [|@eqP_union_l[|@Hind2]] @eqP_union_r @Hind1
  |#e #Hind >sem_star
   @eqP_trans [||@(cat_empty_l … ?)] @cat_ext_l @Hind
  ]
qed.
   
theorem re_embedding: ∀S.∀e:re S. 
  \sem{•(blank S e)} ≐ \sem{e}.
#S #e @eqP_trans [|@sem_bull] >forget_blank 
@eqP_trans [|@eqP_union_r [|@sem_blank]]
@eqP_trans [|@union_comm] @union_empty_r.
qed.

(*
Lifted Operators
 

Plus and bullet have been already lifted from items to pres. We can now 
do a similar job for concatenation ⊙ and Kleene's star ⊛.*)

definition lifted_cat ≝ λS:DeqSet.λe:pre S. 
  lift S (pre_concat_l S eclose e).

notation "e1 ⊙ e2" left associative with precedence 70 for @{'odot $e1 $e2}.

interpretation "lifted cat" 'odot e1 e2 = (lifted_cat ? e1 e2).

lemma odot_true_b : ∀S.∀i1,i2:pitem S.∀b. 
  〈i1,true〉 ⊙ 〈i2,b〉 = 〈i1 · (fst \dots (•i2)),snd \dots (•i2) ∨ b〉.
#S #i1 #i2 #b normalize in ⊢ (??%?); cases (•i2) // 
qed.

lemma odot_false_b : ∀S.∀i1,i2:pitem S.∀b.
  〈i1,false〉 ⊙ 〈i2,b〉 = 〈i1 · i2 ,b〉.
// 
qed.
  
lemma erase_odot:∀S.∀e1,e2:pre S.
  |fst \dots (e1 ⊙ e2)| = |fst \dots e1| · (|fst \dots e2|).
#S * #i1 * * #i2 #b2 // >odot_true_b >erase_dot 
whd in match (fst ???) in ⊢ (???%); whd in match (fst ???) in ⊢ (???%);//  
qed.

(* Let us come to the star operation: *)

definition lk ≝ λS:DeqSet.λe:pre S.
  match e with 
  [ pair i1 b1 ⇒
    match b1 with 
    [true ⇒ 〈(fst \dots (eclose ? i1))^*, true〉
    |false ⇒ 〈i1^*,false〉
    ]
  ]. 

(* notation < "a \sup ⊛" non associative with precedence 90 for @{'lk $a}.*)
interpretation "lk" 'lk a = (lk ? a).
notation "a^⊛" non associative with precedence 90 for @{'lk $a}.

lemma ostar_true: ∀S.∀i:pitem S.
  〈i,true〉^⊛ = 〈(fst \dots (•i))^*, true〉.
// qed.

lemma ostar_false: ∀S.∀i:pitem S.
  〈i,false〉^⊛ = 〈i^*, false〉.
// qed.
  
lemma erase_ostar: ∀S.∀e:pre S.
  |fst \dots (e^⊛)| = |fst \dots e|^*.
#S * #i * whd in match (fst ???) in ⊢ (???%); // qed.

lemma sem_odot_true: ∀S:DeqSet.∀e1:pre S.∀i. 
  \sem{e1 ⊙ 〈i,true〉} ≐ \sem{e1 ▹ i} ∪ { [ ] }.
#S #e1 #i 
cut (e1 ⊙ 〈i,true〉 = 〈fst \dots (e1 ▹ i), snd \dots(e1 ▹ i) ∨ true〉) [//]
#H >H cases (e1 ▹ i) #i1 #b1 cases b1 
  [>sem_pre_true @eqP_trans [||@eqP_sym @union_assoc]
   @eqP_union_l #w normalize % [/2/|* //] 
  |/2/
  ]
qed.

lemma eq_odot_false: ∀S:DeqSet.∀e1:pre S.∀i. 
  e1 ⊙ 〈i,false〉 = e1 ▹ i.
#S #e1 #i  
cut (e1 ⊙ 〈i,false〉 = 〈fst \dots (e1 ▹ i), snd \dots(e1 ▹ i) ∨ false〉) [//]
cases (e1 ▹ i) #i1 #b1 cases b1 #H @H
qed.

(* We conclude this section with the proof of the main semantic properties
of ⊙ and ⊛. *)

lemma sem_odot: 
  ∀S.∀e1,e2: pre S. \sem{e1 ⊙ e2} ≐ \sem{e1}· \sem{|fst \dots e2|} ∪ \sem{e2}.
#S #e1 * #i2 * 
  [>sem_pre_true 
   @eqP_trans [|@sem_odot_true]
   @eqP_trans [||@union_assoc] @eqP_union_r @sem_pcl_aux //
  |>sem_pre_false >eq_odot_false @sem_pcl_aux //
  ]
qed.

theorem sem_ostar: ∀S.∀e:pre S. 
  \sem{e^⊛} ≐  \sem{e} · \sem{|fst \dots e|}^*.
#S * #i #b cases b
  [>sem_pre_true >sem_pre_true >sem_star >erase_bull
   @eqP_trans [|@eqP_union_r[|@cat_ext_l [|@minus_eps_pre_aux //]]]
   @eqP_trans [|@eqP_union_r [|@distr_cat_r]]
   @eqP_trans [||@eqP_sym @distr_cat_r]
   @eqP_trans [|@union_assoc] @eqP_union_l
   @eqP_trans [||@eqP_sym @epsilon_cat_l] @eqP_sym @star_fix_eps 
  |>sem_pre_false >sem_pre_false >sem_star /2/
  ]
qed. 