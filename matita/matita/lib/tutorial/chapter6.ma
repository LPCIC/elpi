
include "tutorial/chapter5.ma".

(*************************** Naive Set Theory *********************************)

(* Given a ``universe'' U (an arbitrary type U:Type), a naive but practical way 
to deal with ``sets'' in U is simply to identify them with their characteristic 
property, that is to as functions of type U → Prop. 

For instance, the empty set is defined by the False predicate; a singleton set 
{x} is defined by the property that its elements are equal to x. *)

definition empty_set ≝ λU:Type[0].λu:U.False.
notation "\emptyv" non associative with precedence 90 for @{'empty_set}.
interpretation "empty set" 'empty_set = (empty_set ?).

definition singleton ≝ λU.λx,u:U.x=u.
(* notation "{x}" non associative with precedence 90 for @{'sing_lang $x}. *)
interpretation "singleton" 'singl x = (singleton ? x).

(* The membership relation is trivial: an element x$ is in the set (defined by 
the property) P if and only if it enjoyes the property, that is, if it holds
(P x). *)

definition member ≝ λU:Type[0].λu:U.λP:U→Prop.P u.

(* The operations of union, intersection, complementation and substraction are 
defined in a straightforward way, in terms of logical operations: *)

definition union ≝ λU:Type[0].λP,Q:U → Prop.λa.P a ∨ Q a.
interpretation "union" 'union a b = (union ? a b).

definition intersection ≝ λU:Type[0].λP,Q:U → Prop.λa.P a ∧ Q a.
interpretation "intersection" 'intersects a b = (intersection ? a b).

definition complement ≝ λU:Type[0].λA:U → Prop.λw.¬ A w.
interpretation "complement" 'not a = (complement ? a).

definition substraction ≝  λU:Type[0].λA,B:U → Prop.λw.A w ∧ ¬ B w.
interpretation "substraction" 'minus a b = (substraction ? a b).

(* More interesting are the notions of subset and equality. Given two sets P and 
Q, P is a subset of Q when any element u in P is also in Q, that is when (P u) 
implies (Q u). *)

definition subset: ∀A:Type[0].∀P,Q:A→Prop.Prop ≝ λA,P,Q.∀a:A.(P a → Q a).

(* Then, two sets P and Q are equal when P ⊆ Q and Q ⊆ P, or equivalently when 
for any element u, P u ↔ Q u. *)

definition eqP ≝ λA:Type[0].λP,Q:A → Prop.∀a:A.P a ↔ Q a.

(* We shall use the infix notation ≐ for the previous notion of equality. *)

(* ≐ is typed as \doteq *)
notation "A ≐ B" non associative with precedence 45 for @{'eqP $A $B}.
interpretation "extensional equality" 'eqP a b = (eqP ? a b).

(* It is important to observe that the eqP is different from Leibniz equality of 
chpater 3. As we already observed, Leibniz equality is a pretty syntactical (or 
intensional) notion, that is a notion concerning the "connotation" of an object
and not its "denotation" (the shape assumed by the object, and not the 
information it is supposed to convey). Intensionality stands in contrast with 
"extensionality", referring to principles that judge objects to be equal if they 
enjoy a given subset of external, observable properties (e.g. the property of 
having the same elements). For instance given two sets A and B we can prove that
A ∪ B ≈ B ∪ A, since they have the same elements, but there is no way to prove 
A ∪ B = B ∪ A.

The main practical consequence is that, while we can always exploit a Leibniz 
equality between two terms t1 and t2 for rewriting one into the other (in fact, 
this is the essence of Leibniz equality), we cannot do the same for an 
extensional equality (we could only rewrite inside propositions ``compatible'' 
with our external observation of the objects). *)

lemma eqP_sym: ∀U.∀A,B:U →Prop. 
  A ≐ B → B ≐ A.
#U #A #B #eqAB #a @iff_sym @eqAB qed.
 
lemma eqP_trans: ∀U.∀A,B,C:U →Prop. 
  A ≐ B → B ≐ C → A ≐ C.
#U #A #B #C #eqAB #eqBC #a @iff_trans // qed.

lemma eqP_union_r: ∀U.∀A,B,C:U →Prop. 
  A ≐ C  → A ∪ B ≐ C ∪ B.
#U #A #B #C #eqAB #a @iff_or_r @eqAB qed.
  
lemma eqP_union_l: ∀U.∀A,B,C:U →Prop. 
  B ≐ C  → A ∪ B ≐ A ∪ C.
#U #A #B #C #eqBC #a @iff_or_l @eqBC qed.

lemma eqP_substract_r: ∀U.∀A,B,C:U →Prop. 
  A ≐ C  → A - B ≐ C - B.
#U #A #B #C #eqAB #a @iff_and_r @eqAB qed.
  
lemma eqP_substract_l: ∀U.∀A,B,C:U →Prop. 
  B ≐ C  → A - B ≐ A - C.
#U #A #B #C #eqBC #a @iff_and_l /2/ qed.

(* set equalities *)
lemma union_empty_r: ∀U.∀A:U→Prop. 
  A ∪ ∅ ≐ A.
#U #A #w % [* // normalize #abs @False_ind /2/ | /2/]
qed.

lemma union_comm : ∀U.∀A,B:U →Prop. 
  A ∪ B ≐ B ∪ A.
#U #A #B #a % * /2/ qed. 

lemma union_assoc: ∀U.∀A,B,C:U → Prop. 
  A ∪ B ∪ C ≐ A ∪ (B ∪ C).
#S #A #B #C #w % [* [* /3/ | /3/] | * [/3/ | * /3/]
qed.  

(*distributivities *)

lemma distribute_intersect : ∀U.∀A,B,C:U→Prop. 
  (A ∪ B) ∩ C ≐ (A ∩ C) ∪ (B ∩ C).
#U #A #B #C #w % [* * /3/ | * * /3/] 
qed.
  
lemma distribute_substract : ∀U.∀A,B,C:U→Prop. 
  (A ∪ B) - C ≐ (A - C) ∪ (B - C).
#U #A #B #C #w % [* * /3/ | * * /3/] 
qed.

(************************ Sets with decidable equality ************************)

(* We say that a property P:A → Prop over a datatype A is decidable when we have 
an effective way to assess the validity of P a for any a:A. As a consequence of 
Goedel incompleteness theorem, not every predicate is decidable: for instance, 
extensional equality on sets is not decidable, in general.  

Decidability can be expressed in several possible ways. A convenient one is to 
state it in terms of the computability of the characterisitc function of the 
predicate P, that is in terms of the existence of a function Pb: A → bool such 
that 
           P a ⇔ Pb a = true
           
Decidability is an important issue, and since equality is an essential 
predicate, it is always interesting to try to understand when a given notion of 
equality is decidable or not. 

In particular, Leibniz equality on inductively generated datastructures is often 
decidable, since we can simply write a decision algorithm by structural 
induction on the terms. For instance we can define characteristic functions for 
booleans and natural numbers in the following way: *)

definition beqb ≝ λb1,b2.
  match b1 with [ true ⇒ b2 | false ⇒ notb b2].

let rec neqb n m ≝ 
match n with 
  [ O ⇒ match m with [ O ⇒ true | S q ⇒ false] 
  | S p ⇒ match m with [ O ⇒ false | S q ⇒ neqb p q]
  ].

(* It is so important to know if Leibniz equality for a given type is decidable 
that turns out to be convenient to pack this information into a single algebraic 
datastructure, called DeqSet: *)

record DeqSet : Type[1] ≝ 
 { carr :> Type[0];
   eqb: carr → carr → bool;
   eqb_true: ∀x,y. (eqb x y = true) ↔ (x = y)}.

notation "a == b" non associative with precedence 45 for @{ 'eqb $a $b }.
interpretation "eqb" 'eqb a b = (eqb ? a b).

(* A DeqSet is simply a record composed by a carrier type carr, a boolean 
function eqb: carr → carr → bool representing the decision algorithm, and a 
proof eqb_true that the decision algorithm is correct. The :> symbol declares 
carr as a coercion from a DeqSet to its carrier type. We use the infix notation 
``=='' for the decidable equality eqb of the carrier.

We can easily prove the following facts: *)

lemma beqb_true_to_eq: ∀b1,b2. beqb b1 b2 = true ↔ b1 = b2.
* * % // normalize #H >H // 
qed.

axiom neqb_true_to_eq: ∀n,m:nat. neqb n m = true ↔ n = m.
(*
#n elim n 
  [#m cases m 
    [% // | #m0 % normalize #H [destruct (H) | @False_ind destruct (H)]] 
  |#n0 #Hind #m cases m 
    [% normalize #H destruct (H) |#m0 >(eq_f … S) % #Heq [@eq_f @(Hind m0)//]
  ]
qed. *)
  
(* Then, we can build the following records: *)
definition DeqBool : DeqSet ≝ mk_DeqSet bool beqb beqb_true_to_eq.
definition DeqNat : DeqSet ≝ mk_DeqSet nat neqb neqb_true_to_eq.

(* Note that, since we declare a coercion from the DeqSet to its carrier, the 
expression 0:DeqNat is well typed, and it is understood by the system as 
0:carr DeqNat - that is, coercions are automatically insterted by the system, if 
required. *)

notation "\P H" non associative with precedence 90 
  for @{(proj1 … (eqb_true ???) $H)}. 

notation "\b H" non associative with precedence 90 
  for @{(proj2 … (eqb_true ???) $H)}. 
  
lemma eqb_false: ∀S:DeqSet.∀a,b:S. 
  (eqb ? a b) = false ↔ a ≠ b.
#S #a #b % #H 
  [@(not_to_not … not_eq_true_false) #H1 <H @sym_eq @(\b H1)
  |cases (true_or_false (eqb ? a b)) // #H1 @False_ind @(absurd … (\P H1) H)
  ]
qed.
 
notation "\Pf H" non associative with precedence 90 
  for @{(proj1 … (eqb_false ???) $H)}. 

notation "\bf H" non associative with precedence 90 
  for @{(proj2 … (eqb_false ???) $H)}. 

(****************************** Unification hints *****************************)

(* Suppose now to write an expression of the following kind:
        b == false
that, after removing the notation, is equivalent to 
        eqb ? b false
The system knows that false is a boolean, so in order to accept the expression, 
it should "figure out" some DeqSet having bool as carrier. This is not a trivial 
operation: Matita should either try to synthetize it (that is a complex 
operation known as narrowing) or look into its database of results for a 
possible solution. 

In this situations, we may suggest the intended solution to Matita using the 
mechanism of unification hints \cite{hints}. The concrete syntax of unification 
hints is a bit involved: we strongly recommend the user to include the file 
"hints_declaration.ma" that allows you to write thing in a more convenient and 
readable way. *)

include "hints_declaration.ma".

(* For instance, the following declaration tells Matita that a solution of the 
equation bool = carr X is X = DeqBool. *)

unification hint 0 ≔ ; 
    X ≟ DeqBool
(* ---------------------------------------- *) ⊢ 
    bool ≡ carr X.

(* Using the previous notation (we suggest the reader to cut and paste it from 
previous hints) the hint is expressed as an inference rule.
The conclusion of the rule is the unification problem that we intend to solve, 
containing one or more variables $X_1,\dots X_b$. The premises of the rule are 
the solutions we are suggesting to Matita. In general, unification hints should 
only be used when there exists just one "intended" (canonical) solution for the 
given equation. 
When you declare a unification hint, Matita verifies it correctness by 
instantiating the unification problem with the hinted solution, and checking the 
convertibility between the two sides of the equation. *)
 
      
example exhint: ∀b:bool. (b == false) = true → b = false. 
#b #H @(\P H).
qed.

(* In a similar way *)

unification hint  0 ≔ b1,b2:bool; 
    X ≟ DeqBool
(* ---------------------------------------- *) ⊢ 
    beqb b1 b2 ≡ eqb X b1 b2.
    
(* pairs *)
definition eq_pairs ≝
  λA,B:DeqSet.λp1,p2:A×B.(fst … p1 == fst … p2) ∧ (snd … p1 == snd … p2).

lemma eq_pairs_true: ∀A,B:DeqSet.∀p1,p2:A×B.
  eq_pairs A B p1 p2 = true ↔ p1 = p2.
#A #B * #a1 #b1 * #a2 #b2 %
  [#H cases (andb_true …H) normalize #eqa #eqb >(\P eqa) >(\P eqb) //
  |#H destruct normalize >(\b (refl … a2)) >(\b (refl … b2)) //
  ]
qed.

definition DeqProd ≝ λA,B:DeqSet.
  mk_DeqSet (A×B) (eq_pairs A B) (eq_pairs_true A B).
  
unification hint  0 ≔ C1,C2; 
    T1 ≟ carr C1,
    T2 ≟ carr C2,
    X ≟ DeqProd C1 C2
(* ---------------------------------------- *) ⊢ 
    T1×T2 ≡ carr X.

unification hint  0 ≔ T1,T2,p1,p2; 
    X ≟ DeqProd T1 T2
(* ---------------------------------------- *) ⊢ 
    eq_pairs T1 T2 p1 p2 ≡ eqb X p1 p2.

example hint2: ∀b1,b2. 
  〈b1,true〉==〈false,b2〉=true → 〈b1,true〉=〈false,b2〉.
#b1 #b2 #H @(\P H)
qed.

(******************************* Prop vs. bool ********************************)

(* It is probably time to make a discussion about "Prop" and "bool", and their 
different roles in a the Calculus of Inductive Constructions. 

Inhabitants of the sort "Prop" are logical propositions. In turn, logical
propositions P:Prop can be inhabitated by their proofs H:P. Since, in general, 
the validity of a property P is not decidable, the role of the proof is to 
provide a witness of the correctness of $P$ that the system can automatically 
check.

On the other hand, bool is just an inductive datatype with two constructors true
and false: these are terms, not types, and cannot be inhabited.
Logical connectives on bool are computable functions, defined by their truth 
tables, using case analysis.
  
Prop and bool are, in a sense, complementary: the former is more suited for 
abstract logical reasoning, while the latter allows, in some situations, for 
brute-force evaluation. 
Suppose for instance that we wish to prove that the 4 ≤ 3!. Starting from the 
definition of the factorial function and properties of the less or equal 
relation, the previous proof could take several steps. Suppose however we proved
the decidability of ≤, that is the existence of a boolean function leb 
reflecting ≤ in the sense that
    
                         n ≤ m ⇔ leb n m = true
             
Then, we could reduce the verification of 4 ≤ 3! to that of leb 4 3! = true that
just requires a mere computation! *)

(******************************** Finite Sets *********************************)

(* A finite set is a record consisting of a DeqSet A, a list of elements of type 
A enumerating all the elements of the set, and the proofs that the enumeration 
does not contain repetitions and is complete. *)

let rec memb (S:DeqSet) (x:S) (l: list S) on l  ≝
  match l with
  [ nil ⇒ false
  | cons a tl ⇒ (x == a) ∨ memb S x tl
  ].
  
lemma memb_hd: ∀S,a,l. memb S a (a::l) = true.
#S #a #l normalize >(proj2 … (eqb_true S …) (refl S a)) //
qed.

lemma memb_cons: ∀S,a,b,l. 
  memb S a l = true → memb S a (b::l) = true.
#S #a #b #l normalize cases (a==b) normalize // 
qed.

lemma memb_single: ∀S,a,x. memb S a [x] = true → a = x.
#S #a #x normalize cases (true_or_false … (a==x)) #H
  [#_ >(\P H) // |>H normalize #abs @False_ind /2/]
qed.

let rec uniqueb (S:DeqSet) l on l : bool ≝
  match l with 
  [ nil ⇒ true
  | cons a tl ⇒ notb (memb S a tl) ∧ uniqueb S tl
  ].

lemma memb_append: ∀S,a,l1,l2. 
memb S a (l1@l2) = true →
  memb S a l1= true ∨ memb S a l2 = true.
#S #a #l1 elim l1 normalize [#l2 #H %2 //] #b #tl #Hind #l2 
cases (a==b) normalize /2/ 
qed. 

lemma memb_append_l1: ∀S,a,l1,l2. 
 memb S a l1= true → memb S a (l1@l2) = true.
#S #a #l1 elim l1 normalize
  [#le #abs @False_ind /2/ |#b #tl #Hind #l2 cases (a==b) normalize /2/ ]
qed. 

lemma memb_append_l2: ∀S,a,l1,l2. 
 memb S a l2= true → memb S a (l1@l2) = true.
#S #a #l1 elim l1 normalize //#b #tl #Hind #l2 cases (a==b) normalize /2/ 
qed. 

lemma memb_map: ∀S1,S2,f,a,l. memb S1 a l= true → 
  memb S2 (f a) (map … f l) = true.
#S1 #S2 #f #a #l elim l normalize [//]
#x #tl #memba cases (true_or_false (a==x))
  [#eqx >eqx >(\P eqx) >(\b (refl … (f x))) normalize //
  |#eqx >eqx cases (f a==f x) normalize /2/
  ]
qed.

lemma memb_compose: ∀S1,S2,S3,op,a1,a2,l1,l2.   
  memb S1 a1 l1 = true → memb S2 a2 l2 = true →
  memb S3 (op a1 a2) (compose S1 S2 S3 op l1 l2) = true.
#S1 #S2 #S3 #op #a1 #a2 #l1 elim l1 [normalize //]
#x #tl #Hind #l2 #memba1 #memba2 cases (orb_true_l … memba1)
  [#eqa1 >(\P eqa1) @memb_append_l1 @memb_map // 
  |#membtl @memb_append_l2 @Hind //
  ]
qed.

lemma uniqueb_append: ∀A,l1,l2. uniqueb A l1 = true → uniqueb A l2 =true → 
  (∀a. memb A a l1 =true → ¬ memb A a l2 =true) → uniqueb A (l1@l2) = true.
#A #l1 elim l1 [normalize //] #a #tl #Hind #l2 #Hatl #Hl2 
#Hmem normalize cut (memb A a (tl@l2)=false)
  [2:#Hcut >Hcut normalize @Hind //
    [@(andb_true_r … Hatl) |#x #Hmemx @Hmem @orb_true_r2 //]
  |@(noteq_to_eqnot ? true) % #Happend cases (memb_append … Happend)
    [#H1 @(absurd … H1) @sym_not_eq @eqnot_to_noteq 
     @sym_eq @(andb_true_l … Hatl)
    |#H @(absurd … H) @Hmem normalize >(\b (refl ? a)) //
    ]
  ]
qed.

lemma memb_map_to_exists: ∀A,B:DeqSet.∀f:A→B.∀l,b. 
  memb ? b (map ?? f l) = true → ∃a. memb ? a l = true ∧ f a = b.
#A #B #f #l elim l 
  [#b normalize #H destruct (H) 
  |#a #tl #Hind #b #H cases (orb_true_l … H) 
    [#eqb @(ex_intro … a) <(\P eqb) % // 
    |#memb cases (Hind … memb) #a * #mema #eqb
     @(ex_intro … a) /3/
    ]
  ]
qed.

lemma memb_map_inj: ∀A,B:DeqSet.∀f:A→B.∀l,a. injective A B f → 
  memb ? (f a) (map ?? f l) = true → memb ? a l = true.
#A #B #f #l #a #injf elim l
  [normalize //
  |#a1 #tl #Hind #Ha cases (orb_true_l … Ha)
    [#eqf @orb_true_r1 @(\b ?)  >(injf … (\P eqf)) //
    |#membtl @orb_true_r2 /2/
    ]
  ]
qed.

lemma unique_map_inj: ∀A,B:DeqSet.∀f:A→B.∀l. injective A B f → 
  uniqueb A l = true → uniqueb B (map ?? f l) = true .
#A #B #f #l #injf elim l 
  [normalize //
  |#a #tl #Hind #Htl @true_to_andb_true
    [@sym_eq @noteq_to_eqnot @sym_not_eq 
     @(not_to_not ?? (memb_map_inj … injf …) )
     <(andb_true_l ?? Htl) /2/
    |@Hind @(andb_true_r ?? Htl)
    ]
  ]
qed.

record FinSet : Type[1] ≝ 
{ FinSetcarr:> DeqSet;
  enum: list FinSetcarr;
  enum_unique: uniqueb FinSetcarr enum = true;
  enum_complete : ∀x:FinSetcarr. memb ? x enum = true}.
  
(* The library provides many operations for building new FinSet by composing
existing ones: for example, if A and B have type FinSet, then also option A, 
A × B and A + B are finite sets. In all these cases, unification hints are used 
to suggest the intended finite set structure associated with them, that makes 
their use quite transparent to the user.*)

definition enum_prod ≝ λA,B:DeqSet.λl1:list A.λl2:list B.
  compose ??? (pair A B) l1 l2.
  
lemma enum_prod_unique: ∀A,B,l1,l2. 
  uniqueb A l1 = true → uniqueb B l2 = true →
  uniqueb ? (enum_prod A B l1 l2) = true.
#A #B #l1 elim l1 //
  #a #tl #Hind #l2 #H1 #H2 @uniqueb_append 
  [@unique_map_inj // #b1 #b2 #H3 destruct (H3) //
  |@Hind // @(andb_true_r … H1)
  |#p #H3 cases (memb_map_to_exists … H3) #b * 
   #Hmemb #eqp <eqp @(not_to_not ? (memb ? a tl = true))
    [2: @sym_not_eq @eqnot_to_noteq @sym_eq @(andb_true_l … H1)
    |elim tl 
      [normalize //
      |#a1 #tl1 #Hind2 #H4 cases (memb_append … H4) -H4 #H4
        [cases (memb_map_to_exists … H4) #b1 * #memb1 #H destruct (H)
         normalize >(\b (refl ? a)) //
        |@orb_true_r2 @Hind2 @H4
        ]
      ]
    ]
  ]
qed.
  

lemma enum_prod_complete:∀A,B:DeqSet.∀l1,l2.
  (∀a. memb A a l1 = true) → (∀b.memb B b l2 = true) →
    ∀p. memb ? p (enum_prod A B l1 l2) = true.
#A #B #l1 #l2 #Hl1 #Hl2 * #a #b @memb_compose // 
qed.

definition FinProd ≝ 
λA,B:FinSet.mk_FinSet (DeqProd A B)
  (enum_prod A B (enum A) (enum B)) 
  (enum_prod_unique A B … (enum_unique A) (enum_unique B)) 
  (enum_prod_complete A B … (enum_complete A) (enum_complete B)).

unification hint  0 ≔ C1,C2; 
    T1 ≟ FinSetcarr C1,
    T2 ≟ FinSetcarr C2,
    X ≟ FinProd C1 C2
(* ---------------------------------------- *) ⊢ 
    T1×T2 ≡ FinSetcarr X.

(* A particularly intersting case is that of the arrow type A → B. We may define 
the graph of f:A → B, as the set (sigma type) of all pairs 〈a,b〉 such that 
f a = b. *)

definition graph_of ≝ λA,B.λf:A→B. Σp:A×B.f (fst … p) = snd … p.

(* In case the equality is decidable, we may effectively enumerate all elements 
of the graph by simply filtering from pairs in A × B those satisfying the 
test λp.f (fst … p) == snd … p: *)

definition graph_enum ≝ λA,B:FinSet.λf:A→B. 
  filter ? (λp.f (fst … p) == snd … p) (enum (FinProd A B)).

(* The proofs that this enumeration does not contain repetitions and
is complete are straightforward. *)
