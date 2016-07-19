(*
Coinductive Types and Predicates
*)

include "basics/lists/list.ma".
include "tutorial/chapter12.ma".

(* The only primitive data types of Matita are dependent products and universes.
So far every other user defined data type has been an inductive type. An
inductive type is declared by giving its list of constructors (or introduction
rules in the case of predicates). An inhabitant of an inductive type is obtained
composing together a finite number of constructors and data of other types,
according to the type of the constructors. Therefore all inhabitants of inductive
types are essentially finite objects. Natural numbers, lists, trees, states of
a DFA, letters of an alphabet are all finite and can be defined inductively.

If you think of an inhabitant of an inductive type as a tree of a certain shape,
whose nodes are constructors, the only trees can be represented are trees of
finite height. Note, however, that it is possible to have trees of infinite
width by putting in the argument of a constructor of a type I an enumeration
of elements of I (e.g. ℕ → I). *)

(* Example of an infinitely branching tree of elements of type A stored in
the nodes: *)
inductive infbrtree (A: Type[0]) : Type[0] ≝
   Nil: infbrtree A
 | Node: A → (ℕ → infbrtree A) → infbrtree A.

(* Example: the tree of natural numbers whose root holds 0 and has as children
   the leafs 1,2,3,… *)
example infbrtree_ex ≝ Node ℕ 0 (λn. Node ℕ (S n) (λ_.Nil ℕ)).

(*** Infinite data types via functions ***)

(* In mathematics and less frequently in computer science there is the need to
also represent and manipulate types of infinite objects. Typical examples are:
sequences, real numbers (a special case of sequences), data streams (e.g. as
read from a network interface), traces of diverging computations of a program,
etc. One possible representation, used in mathematics since a long time, is
to describe an infinite object by means of an infinite collection of
approximations (also called observations). Often, the infinite collection can
be structured in a sequence, identified as a function from the domain of natural
numbers. *)

(* Example 1: sequences of elements of type A *)
definition seq : Type[0] → Type[0] ≝ λA:Type[0]. ℕ → A.

(* Example 2: Real numbers as Cauchy sequences and their addition. *)
(* First we axiomatize the relevant properties of rational numbers. *)
axiom Q: Type[0].
axiom Qdist: Q → Q → Q.
axiom symmetric_Qdist: ∀x,y. Qdist x y = Qdist y x.
axiom Qleq: Q → Q → Prop.
interpretation "Qleq" 'leq x y = (Qleq x y).
axiom transitive_Qleq: transitive … Qleq.
axiom Qplus: Q → Q → Q.
interpretation "Qplus" 'plus x y = (Qplus x y).
axiom Qleq_Qplus:
 ∀qa1,qb1,qa2,qb2. qa1 ≤ qb1 → qa2 ≤ qb2 → qa1 + qa2 ≤ qb1 + qb2.
axiom Qdist_Qplus:
 ∀qa1,qb1,qa2,qb2. Qdist (qa1 + qa2) (qb1 + qb2) ≤ Qdist qa1 qb1 + Qdist qa2 qb2.
axiom Qhalve: Q → Q.
axiom Qplus_Qhalve_Qhalve: ∀q. Qhalve q + Qhalve q = q.
axiom triangular_Qdist: ∀x,y,z. Qdist x z ≤ Qdist x y + Qdist y z.

(* A sequence of rationals. *)
definition Qseq: Type[0] ≝ seq Q.

(* The Cauchy property *)
definition Cauchy: Qseq → Prop ≝
 λR:Qseq. ∀eps. ∃n. ∀i,j. n ≤ i → n ≤ j → Qdist (R i) (R j) ≤ eps.

(* A real number is an equivalence class of Cauchy sequences. In type theory
 we can define R as a setoid whose carrier R_ is the type of Cauchy sequences. *)
record R_: Type[0] ≝
 { r: Qseq
 ; isCauchy: Cauchy r
 }.

(* Two sequences are equal when for every epsilon they are eventually pointwise
 closer than epsilon. *)
definition R : setoid ≝
 mk_setoid R_
  (mk_equivalence_relation …
   (λr1,r2:R_. ∀eps. ∃n. ∀i. n ≤ i → Qdist (r r1 i) (r r2 i) ≤ eps) …).
[ (* transitivity *) #x #y #z #H1 #H2 #eps cases (H1 (Qhalve eps)) #i -H1 #H1
  cases (H2 (Qhalve eps)) #j -H2 #H2 %{(max i j)} #l #Hmax
  <(Qplus_Qhalve_Qhalve eps) @transitive_Qleq
  [3: @(Qleq_Qplus … (H1 l …) (H2 l …)) /2 by le_maxl,le_maxr/
  |2: // ]
| (* symmetry *) #x #y #H #eps cases (H eps) /3 by ex_intro/
| (* reflexivity *) #x #eps cases (isCauchy x eps) /3 by ex_intro/ ]
qed.

unification hint 0 ≔ ;
    X ≟ R
(* ---------------------------------------- *) ⊢
    R_ ≡ carrier R.

(* The following coercion is used to write r n to extract the n-th approximation
 from the real number r *)
coercion R_to_fun : ∀r:R. ℕ → Q ≝ r on _r:R to ?. 

(* Adding two real numbers just requires pointwise addition of the 
 approximations. The proof that the resulting sequence is Cauchy is the standard
 one: to obtain an approximation up to eps it is necessary to approximate both
 summands up to eps/2. *)
definition Rplus_: R_ → R_ → R_ ≝
 λr1,r2. mk_R_ (λn. r1 n + r2 n) ….
 #eps
 cases (isCauchy r1 (Qhalve eps)) #n1 #H1
 cases (isCauchy r2 (Qhalve eps)) #n2 #H2
 %{(max n1 n2)} #i #j #K1 #K2 @(transitive_Qleq … (Qdist_Qplus …))
 <(Qplus_Qhalve_Qhalve eps) @Qleq_Qplus [@H1 @le_maxl | @H2 @le_maxr]
 [2,6: @K1 |4,8: @K2]
qed.

(* We lift Rplus_ to a morphism by proving that it respects the equality for
 real numbers. We closely follow the usual mathematical proof: to compute the
 sum up to epsilon it is sufficient to fetch the arguments at precision
 epsilon/2. *)
definition Rplus: R ⤞ R ⤞ R ≝
 mk_bin_morphism … Rplus_ ….
 #x1 #x2 #y1 #y2 #Hx #Hy #eps
 cases (Hx (Qhalve eps)) #i -Hx #Hx
 cases (Hy (Qhalve eps)) #j -Hy #Hy
 %{(max i j)} #l #Hmax <(Qplus_Qhalve_Qhalve eps) @transitive_Qleq
 [3: @(Qleq_Qplus … (Hx l …) (Hy l …)) /2 by le_maxl,le_maxr/
 |2: // ]
qed.

(* Example 3: traces of a program *)
(* Let us introduce a very simple programming language whose instructions
   can test and set a single implicit variable. *)
inductive instr: Type[0] ≝
   p_set: ℕ → instr                 (* sets the variable to a constant *)
 | p_incr: instr                    (* increments the variable *)
 | p_while: list instr → instr.     (* repeats until the variable is 0 *)

(* The status of a program as the values of the variable and the list of
 instructions to be executed. *)
definition state ≝ ℕ × (list instr).

(* The transition function from a state to the next one. *)
inductive next: state → state → Prop ≝
   n_set: ∀n,k,o. next 〈o,(p_set n)::k〉 〈n,k〉
 | n_incr: ∀k,o. next 〈o,p_incr::k〉 〈S o,k〉
 | n_while_exit: ∀b,k. next 〈0,(p_while b)::k〉 〈0,k〉
 | n_while_loop: ∀b,k,o. next 〈S o,(p_while b)::k〉 〈S o,b@(p_while b)::k〉.

(* A diverging trace is a sequence of states such that the n+1-th state is
 obtained executing one step from the n-th state *)
record div_trace: Type[0] ≝
 { div_tr: seq state
 ; div_well_formed: ∀n. next (div_tr n) (div_tr (S n))
 }.

(* The previous definition of trace is not computable: we cannot write
 a program that given an initial state returns its trace. To write that function,
 we first write a computable version of next, called step. *)
definition step: state → option state ≝
 λs. let 〈o,k〉 ≝ s in
  match k with
   [ nil ⇒ None ?
   | cons hd k ⇒
      Some … match hd with
      [ p_set n ⇒ 〈n,k〉
      | p_incr ⇒ 〈S o,k〉
      | p_while b ⇒
         match o with
         [ O ⇒ 〈0,k〉
         | S p ⇒ 〈S p,b@(p_while b)::k〉 ]]].

theorem step_next: ∀o,n. step o = Some … n → next o n.
 * #o * [ #n normalize #abs destruct ]
 * normalize
 [ #n #tl * #n' #tl'
 | #tl * #n' #tl'
 | #b #tl * #n' #tl' cases o normalize [2: #r]]
 #EQ destruct //
qed.

theorem next_step: ∀o,n. next o n → step o = Some … n.
 * #o #k * #n #k' #H inversion H normalize
 [ #v #tl #n'
 | #tl #n'
 | #b #tl]
 #EQ1 #EQ2 //
qed.
  
(* Termination is the archetipal undecidable problem. Therefore there is no
 function that given an initial state returns the diverging trace if the program
 diverges or fails in case of error. The best we can do is to give an alternative
 definition of trace that captures both diverging and converging computations. *)
record trace: Type[0] ≝
 { tr: seq (option state)
 ; well_formed: ∀n,s. tr n = Some … s → tr (S n) = step s
 }.

(* The trace is diverging if every state is not final. *)
definition diverging: trace → Prop ≝
 λt. ∀n. tr t n ≠ None ?.

(* The two definitions of diverging traces are equivalent. *)
theorem div_trace_to_diverging_trace:
 ∀d: div_trace. ∃t: trace. diverging t ∧ tr t 0 = Some … (div_tr d 0).
 #d %{(mk_trace (λn.Some ? (div_tr d n)) …)}
 [2: % // #n % #abs destruct
 | #n #s #EQ destruct lapply (div_well_formed d n) /2 by div_well_formed, next_step/ ]
qed.

theorem diverging_trace_to_div_trace:
 ∀t: trace. diverging t → ∃d: div_trace. tr t 0 = Some … (div_tr d 0).
 #t #H %
 [ % [ #n lapply (H n) -H cases (tr t n) [ * #abs cases (abs …) // ] #s #_ @s
 | #n  lapply (well_formed t n)
   lapply (H n) cases (tr t n) normalize [ * #abs cases (abs …) // ]
   * #o #k #_ lapply (H (S n)) -H
   cases (tr t (S n)) normalize
   [ * #abs cases (abs …) // ] * #o' #k' #_ #EQ lapply (EQ … (refl …)) -EQ
     normalize cases k normalize [ #abs destruct ] #hd #tl #EQ destruct -EQ
     @step_next >e0 // ]
 | lapply (H O) -H cases (tr t O) [ * #abs cases (abs …) // ] // ]
qed.

(* However, given an initial state we can always compute a trace.
   Note that every time the n-th element of the trace is accessed, all the
   elements in position ≤ n are computed too. *)
let rec compute_trace_seq (s:state) (n:nat) on n : option state ≝
 match n with
 [ O ⇒ Some … s
 | S m ⇒
    match compute_trace_seq s m with
    [ None ⇒ None …
    | Some o ⇒ step o ]].

definition compute_trace: ∀s:state. Σt:trace. tr t 0 = Some … s.
 #s %
 [ %{(compute_trace_seq s)}
   #n #o elim n [ whd in ⊢ (??%? → ??%?); #EQ destruct // ]
   -n #n #_ #H whd in ; whd in ⊢ (??%?); >H //
 | // ]
qed.

(*** Infinite data types as coinductive types ***)

(* All the previous examples were handled very easily via sequences
 declared as functions. A few critics can be made to this approach though:
 1. the sequence allows for random access. In many situations, however, the
    elements of the sequence are meant to be read one after the other, in
    increasing order of their position. Moreover, the elements are meant to be
    consumed (read) linearly, i.e. just once. This suggests a more efficient
    implementation where sequences are implemented with state machines that
    emit the next value and enter a new state every time they are read. Indeed,
    some programming languages like OCaml differentiate (possibly infinite)
    lists, that are immutable, from mutable streams whose only access operation
    yields the head and turns the stream into its tail. Data streams read from
    the network are a typical example of streams: the previously read values are
    not automatically memoized and are lost if not saved when read. Files on
    disk are also usually read via streams to avoid keeping all of them in main
    memory. Another typical case where streams are used is that of diverging
    computations: in place of generating at once an infinite sequence of values,
    a function is turned into a stream and asking the next element of the stream
    runs one more iteration of the function to produce the next output (often
    an approximation).
 2. if a sequence computes the n-th entry by recursively calling itself on every
    entry less than n, accessing the n-th entry requires re-computation of all
    entries in position ≤ n, which is very inefficient. 
 3. by representing an infinite object as a collection of approximations, the
    structure of the object is lost. This was not evident in the previous
    examples because in all cases the intrinsic structure of the datatype was
    just that of being ordered and sequences capture the order well. Imagine,
    however, that we want to represent an infinite binary tree of elements of
    type A with the previous technique. We need to associate to each position
    in the infinite tree an element of type A. A position in the tree is itself
    a path from the root to the node of interest. Therefore the infinite tree
    is represented as the function (ℕ → 𝔹) → A where 𝔹 are the booleans and the
    tree structure is already less clear. Suppose now that the binary tree may
    not be full, i.e. some nodes can have less than two children. Representing
    such a tree is definitely harder. We may for example use the data type
    (N → 𝔹) → option A where None would be associated to the position
    b1 ... bn if a node in such position does not exist. However, we would need
    to add the invariant that if b1 ... bn is undefined (i.e. assigned to None),
    so are all suffixes b1 ... bn b_{n+1} ... b_{n+j}.

 The previous observations suggest the need for primitive infinite datatypes
 in the language, usually called coinductive types or codata. Matita allows
 to declare coinductive type with the same syntax used for inductive types,
 just replacing the keywork inductive with coinductive. Semantically, the two
 declarations differ because a coinductive type also contains infinite
 inhabitants that respect the typechecking rules.
*)

(* Example 1 revisited: non terminated streams of elements of type A *)
coinductive streamseq (A: Type[0]) : Type[0] ≝
 sscons: A → streamseq A → streamseq A.

(* Coinductive types can be inhabited by infinite data using coinductive
   definitions, introduced by the keyword let corec. The syntax of let corec
   definitions is the same of let rec definitions, but for the declarations
   of the recursive argument. While let rec definitions are recursive definition
   that are strictly decreasing on the recursive argument, let corec definitions
   are productive recursive definitions. A recursive definition is productive
   if, when fully applied to its arguments, it reduces in a finite amount of time
   to a constructor of a coinductive type.
   
   Let's see some simple examples of coinductive definitions of corecursive
   streamseqs. *)

(* The streamseq 0 0 0 ...
   Note that all_zeros is not a function and does not have any argument.
   The definition is clearly productive because it immediately reduces to
   the constructor sscons. *)
let corec all_zeros: streamseq nat ≝ sscons nat 0 all_zeros.

(* The streamseq n (n+1) (n+2) ...
   The definition behaves like an automaton with state n. When the
   streamseq is pattern matched, the current value n is returned as head
   of the streamseq and the tail of the streamseq is the automaton with
   state (S n). Therefore obtaining the n-th tail of the stream requires O(n)
   operation, but every further access to its value only costs O(1). Moreover,
   in the future the implementation of Matita could automatically memoize
   streams so that obtaining the n-th element would also be an O(1) operation
   if the same element was previously accessed at least once. This is what
   is currently done in the implementation of the Coq system for example.
*)
let corec from_n (n:ℕ) : streamseq nat ≝ sscons … n (from_n (S n)).

(* In order to retrieve the n-th element from a streamseq we can write a
   function recursive over n. *)
let rec streamseq_nth (A: Type[0]) (s: streamseq A) (n:ℕ) on n : A ≝
 match s with [ sscons hd tl ⇒
  match n with [ O ⇒ hd | S m ⇒ streamseq_nth … tl m ]]. 

(* Any sequence can be turned into the equivalent streamseq and the other
   way around. *)
let corec streamseq_of_seq (A: Type[0]) (s: seq A) (n:ℕ) : streamseq A ≝
 sscons … (s n) (streamseq_of_seq A s (S n)).

lemma streamseq_of_seq_ok:
 ∀A:Type[0]. ∀s: seq A. ∀m,n.
  streamseq_nth A (streamseq_of_seq … s n) m = s (m+n).
 #A #s #m elim m normalize //
qed.

definition seq_of_streamseq: ∀A:Type[0]. streamseq A → seq A ≝ streamseq_nth.

lemma seq_of_streamseq_ok:
 ∀A:Type[0]. ∀s: streamseq A. ∀n. seq_of_streamseq … s n = streamseq_nth … s n.
 //
qed.

(* Example 2 revisited: Real numbers as Cauchy sequences and their addition.
   We closely follow example 2 replacing sequences with streamseqs.
*)

definition Qstreamseq: Type[0] ≝ streamseq Q.

definition Qstreamseq_nth ≝ streamseq_nth Q.

(* The Cauchy property *)
definition Cauchy': Qstreamseq → Prop ≝
 λR:Qstreamseq. ∀eps. ∃n. ∀i,j. n ≤ i → n ≤ j → Qdist (Qstreamseq_nth R i) (Qstreamseq_nth R j) ≤ eps.

(* A real number is an equivalence class of Cauchy sequences. In type theory
 we can define R' as a setoid whose carrier R_' is the type of Cauchy sequences. *)
record R_': Type[0] ≝
 { r': Qstreamseq
 ; isCauchy': Cauchy' r'
 }.

(* Two sequences are equal when for every epsilon they are eventually pointwise
 closer than epsilon. The script is exactly the same already used when we
 defined R using functions. *)
definition R' : setoid ≝
 mk_setoid R_'
  (mk_equivalence_relation …
   (λr1,r2:R_'. ∀eps. ∃n. ∀i. n ≤ i →
    Qdist (Qstreamseq_nth (r' r1) i) (Qstreamseq_nth (r' r2) i) ≤ eps) …).
[ (* transitivity *) #x #y #z #H1 #H2 #eps cases (H1 (Qhalve eps)) #i -H1 #H1
  cases (H2 (Qhalve eps)) #j -H2 #H2 %{(max i j)} #l #Hmax
  <(Qplus_Qhalve_Qhalve eps) @transitive_Qleq
  [3: @(Qleq_Qplus … (H1 l …) (H2 l …)) /2 by le_maxl,le_maxr/
  |2: // ]
| (* symmetry *) #x #y #H #eps cases (H eps) /3 by ex_intro/
| (* reflexivity *) #x #eps cases (isCauchy' x eps) /3 by ex_intro/ ]
qed.

unification hint 0 ≔ ;
    X ≟ R'
(* ---------------------------------------- *) ⊢
    R_' ≡ carrier R'.

(* The following coercion is used to write r n to extract the n-th approximation
 from the real number r *)
coercion R_to_fun' : ∀r:R'. ℕ → Q ≝ (λr. Qstreamseq_nth (r' r)) on _r:R' to ?. 

(* Pointwise addition over Qstreamseq defined by corecursion.
   The definition is productive because, when Rplus_streamseq is applied to
   two closed values of type Qstreamseq, it will reduce to sscons. *)
let corec Rplus_streamseq (x:Qstreamseq) (y:Qstreamseq) : Qstreamseq ≝
 match x with [ sscons hdx tlx ⇒
 match y with [ sscons hdy tly ⇒
  sscons … (hdx + hdy) (Rplus_streamseq tlx tly) ]].

(* The following lemma was for free using sequences. In the case of streamseqs
 it must be proved by induction over the index because Qstreamseq_nth is defined by
 recursion over the index. *)
lemma Qstreamseq_nth_Rplus_streamseq:
 ∀i,x,y.
  Qstreamseq_nth (Rplus_streamseq x y) i = Qstreamseq_nth x i + Qstreamseq_nth y i.
 #i elim i [2: #j #IH] * #xhd #xtl * #yhd #ytl // normalize @IH
qed.

(* The proof that the resulting sequence is Cauchy is exactly the same we
 used for sequences, up to two applications of the previous lemma. *)
definition Rplus_': R_' → R_' → R_' ≝
 λr1,r2. mk_R_' (Rplus_streamseq (r' r1) (r' r2)) ….
 #eps
 cases (isCauchy' r1 (Qhalve eps)) #n1 #H1
 cases (isCauchy' r2 (Qhalve eps)) #n2 #H2
 %{(max n1 n2)} #i #j #K1 #K2
 >Qstreamseq_nth_Rplus_streamseq >Qstreamseq_nth_Rplus_streamseq
 @(transitive_Qleq … (Qdist_Qplus …))
 <(Qplus_Qhalve_Qhalve eps) @Qleq_Qplus [@H1 @le_maxl | @H2 @le_maxr]
 [2,6: @K1 |4,8: @K2]
qed.

(* We lift Rplus_' to a morphism by proving that it respects the equality for
 real numbers. The script is exactly the same we used to lift Rplus_, but for
 two applications of Qstreamseq_nth_Rplus_streamseq. *)
definition Rplus': R' ⤞ R' ⤞ R' ≝
 mk_bin_morphism … Rplus_' ….
 #x1 #x2 #y1 #y2 #Hx #Hy #eps
 cases (Hx (Qhalve eps)) #i -Hx #Hx
 cases (Hy (Qhalve eps)) #j -Hy #Hy
 %{(max i j)} #l #Hmax <(Qplus_Qhalve_Qhalve eps) @transitive_Qleq
 [3: @(Qleq_Qplus … (Hx l …) (Hy l …)) /2 by le_maxl,le_maxr/
 |2: >Qstreamseq_nth_Rplus_streamseq >Qstreamseq_nth_Rplus_streamseq // ]
qed.

(***** Intermezzo: the dynamics of coinductive data ********)

(* Let corec definitions, like let rec definitions, are a form of recursive
 definition where the definiens occurs in the definiendum. Matita compares
 types up to reduction and reduction always allows the expansion of non recursive
 definitions. If it also allowed the expansion of recursive definitions, reduction
 could diverge and type checking would become undecidable. For example,
 we defined all_zeros as "sscons … 0 all_zeros". If the system expanded all
 occurrences of all_zeros, it would expand it forever to
 "sscons … 0 (sscons … 0 (sscons … 0 …))".
 
 In order to avoid divergence, recursive definitions are only expanded when a
 certain condition is met. In the case of a let-rec defined function f that is
 recursive on its n-th argument, f is only expanded when it occurs in an
 application (f t1 ... tn ...) and tn is (the application of) a constructor.
 Termination is guaranteed by the combination of this restriction and f being
 guarded by destructors: the application (f t1 ... tn ...) can reduce to a term
 that contains another application (f t1' ... tn' ...) but the size of tn'
 (roughly the number of nested constructors) will be smaller than the size of tn
 eventually leading to termination.

 Dual restrictions are put on let corec definitions. If f is a let-rec defined
 term, f is only expanded when it occurs in the term "match f t1 ... tn with ...".
 To better see the duality, that is not syntactically perfect, note that: in
 the recursive case f destructs terms and is expanded only when applied to a
 constructor; in the co-recursive case f constructs terms and is expanded only
 when it becomes argument of the match destructor. Termination is guaranteed
 by the combination of this restriction and f being productive: the term
 "match f t1 ... tn ... with" will reduce in a finite amount of time to
 a match applied to a constructor, whose reduction can expose another application
 of f, but not another "match f t1' .. tn' ... width". Therefore, since no
 new matches around f can be created by reduction, the number of
 destructors that surrounds the application of f decreases at every step,
 eventually leading to termination.
 
 Even if a coinductively defined f does not reduce in every context to its
 definiendum, it is possible to prove that the definiens is equal to its
 definiendum. The trick is to prove first an eta-expansion lemma for the
 inductive type that states that an inhabitant of the inductive type is
 equal to the one obtained destructing and rebuilding it via a match. The proof
 is simply by cases over the inhabitant. Let's see an example. *)

lemma eta_streamseq:
 ∀A:Type[0]. ∀s: streamseq A.
  match s with [ sscons hd tl ⇒ sscons … hd tl ] = s.
 #A * //
qed.

(* In order to prove now that the definiens of all_zeros is equal to its
 definiendum, it suffices to rewrite it using the eta_streamseq lemma in order
 to insert around the definiens the match destructor that triggers its
 expansion. *)
lemma all_zeros_expansion: all_zeros = sscons … 0 all_zeros.
 <(eta_streamseq ? all_zeros) in ⊢ (??%?); //
qed.

(* Expansions lemmas as the one just presented are almost always required to
 progress in non trivial proofs, as we will see in the next example. Instead
 the equivalent expansions lemmas for let-rec definitions are rarely required.
*)

(* Example 3 revisited: traces of a program. *)

(* A diverging trace is a streamseq of states such that the n+1-th state is
 obtained executing one step from the n-th state. The definition of
 div_well_formed' is the same we already used for sequences, but on
 streamseqs. *)

definition div_well_formed' : streamseq state → Prop ≝
 λs: streamseq state.
  ∀n. next (streamseq_nth … s n) (streamseq_nth … s (S n)). 

record div_trace': Type[0] ≝
 { div_tr':> streamseq state
 ; div_well_formed'': div_well_formed' div_tr' 
 }.

(* The well formedness predicate over streamseq can also be redefined using as a
 coinductive predicate. A streamseq of states is well formed if the second
 element is the next of the first and the stream without the first element
 is recursively well formed. *)
coinductive div_well_formed_co: streamseq state → Prop ≝
 is_next:
  ∀hd1:state. ∀hd2:state. ∀tl:streamseq state.
   next hd1 hd2 → div_well_formed_co (sscons … hd2 tl) →
    div_well_formed_co (sscons … hd1 (sscons … hd2 tl)).

(* Note that Matita automatically proves the inversion principles for every
 coinductive type, but no general coinduction principle. That means that
 the elim tactic does not work when applied to a coinductive type. Inversion
 and cases are the only ways to eliminate a coinductive hypothesis. *)

(* A proof of div_well_formed cannot be built stacking a finite
 number of constructors. The type can only be inhabited by a coinductive
 definition. As an example, we show the equivalence between the two
 definitions of well formedness for streamseqs. *)
 
(* A div_well_formed' stream is also div_well_formed_co. We write the proof
 term explicitly, omitting the subterms that prove "next hd1 hd2" and
 "div_well_formed' (sscond … hd2 tl)". Therefore we will obtain two proof
 obligations. The given proof term is productive: if we apply it to a closed
 term of type streamseq state and a proof that it is well formed, the two
 matches in head position will reduce and the lambda-abstraction will be
 consumed, exposing the is_next constructor. *)
 
let corec div_well_formed_to_div_well_formed_co
 (s: streamseq state): div_well_formed' s → div_well_formed_co s ≝
 match s with [ sscons hd1 tl1 ⇒
  match tl1 with [ sscons hd2 tl ⇒
   λH: div_well_formed' (sscons … hd1 (sscons … hd2 tl)).
    is_next … (div_well_formed_to_div_well_formed_co (sscons … hd2 tl) …) ]].
[ (* First proof obligation: next hd1 hd2 *) @(H 0)
| (* Second proof obligation: div_well_formed' (sscons … hd2 tl) *) @(λn. H (S n)) ]
qed.  

(* A div_well_formed_co stream is also div_well_formed'. This time the proof is
 by induction over the index and inversion over the div_well_formed_co
 hypothesis. *)
theorem div_well_formed_co_to_div_well_formed:
 ∀s: streamseq state. div_well_formed_co s → div_well_formed' s.
 #s #H #n lapply H -H lapply s -s elim n [2: #m #IH]
 * #hd1 * #hd2 #tl normalize #H inversion H #hd1' #hd2' #tl' #Hnext #Hwf
 #eq destruct /2/
qed.

(* Like for sequences, because of undecidability of termination there is no
 function that given an initial state returns the diverging trace if the program
 diverges or fails in case of error. We need a new data type to represent a
 possibly infinite, possibly terminated stream of elements. Such data type is
 usually called stream and can be defined elegantly as a coinductive type. *)
coinductive stream (A: Type[0]) : Type[0] ≝
   snil: stream A
 | scons: A → stream A → stream A.

(* The following lemma will be used to unblock blocked reductions, as
 previously explained for eta_streamseq. *)
lemma eta_stream:
 ∀A:Type[0]. ∀s: stream A.
  match s with [ snil ⇒ snil … | scons hd tl ⇒ scons … hd tl ] = s.
 #A * //
qed.

(* The definition of trace based on streams is more natural than that based
 on sequences of optional states because there is no need of the invariant that
 a None state is followed only by None states (to represent a terminated
 sequence). Indeed, this is the first example where working with coinductive
 types seems to yield advantages in terms of simplicity of the formalization.
 However, in order to give the definition we first need to coinductively define
 the well_formedness predicate, whose definition is more complex than the
 previous one. *)
coinductive well_formed': stream state → Prop ≝
   wf_snil: ∀s. step s = None … → well_formed' (scons … s (snil …))
 | wf_scons:
    ∀hd1,hd2,tl.
     step hd1 = Some … hd2 →
      well_formed' (scons … hd2 tl) →
       well_formed' (scons … hd1 (scons … hd2 tl)).

(* Note: we could have equivalently defined well_formed' avoiding coinduction
 by defining a recursive function to retrieve the n-th element of the stream,
 if any. From now on we will stick to coinductive predicates only to show more
 examples of usage of coinduction. In a formalization, however, it is always
 better to explore several alternatives and see which ones work best for the
 problem at hand. *)

record trace': Type[0] ≝
 { tr':> stream state
 ; well_formed'': well_formed' tr'
 }.

(* The trace is diverging if every state is not final. Again, we show here
 a coinductive definition. *)
coinductive diverging': stream state → Prop ≝
 mk_diverging': ∀hd,tl. diverging' tl → diverging' (scons … hd tl).

(* The two coinductive definitions of diverging traces are equivalent.
 To state the two results we first need a function to retrieve the head
 from traces and diverging traces. *)
definition head_of_streamseq: ∀A:Type[0]. streamseq A → A ≝
 λA,s. match s with [ sscons hd _ ⇒ hd ].

definition head_of_stream: ∀A:Type[0]. stream A → option A ≝
 λA,s. match s with [ snil ⇒ None … | scons hd _ ⇒ Some … hd ].

(* A streamseq can be extracted from a diverging stream using corecursion. *)
let corec mk_diverging_trace_to_div_trace'
 (s: stream state) : diverging' s → streamseq state ≝
 match s return λs. diverging' s → streamseq state
 with
 [ snil ⇒ λabs: diverging' (snil …). ?
 | scons hd tl ⇒ λH. sscons ? hd (mk_diverging_trace_to_div_trace' tl …) ].
 [ cases (?:False) inversion abs #hd #tl #_ #abs' destruct
 | inversion H #hd' #tl' #K #eq destruct @K ]
qed.

(* An expansion lemma will be needed soon. *)
lemma mk_diverging_trace_to_div_trace_expansion:
 ∀hd,tl,H. ∃K.
  mk_diverging_trace_to_div_trace' (scons state hd tl) H =
   sscons … hd (mk_diverging_trace_to_div_trace' tl K).
 #hd #tl #H cases (eta_streamseq … (mk_diverging_trace_to_div_trace' ??)) /2/
qed.

(* CSC: BUG CHE APPARE NEL PROSSIMO LEMMA AL MOMENTO DELLA QED. IL DEMONE
 SERVE PER DEBUGGARE *)
axiom daemon: False.

(* To complete the proof we need a final lemma: streamseqs extracted from
 well formed diverging streams are well formed too. The definition is mostly
 interactive because we need to use the expansion lemma above to rewrite
 the type of the scons branch. Otherwise, Matita rejects the term as ill-typed *) 
let corec div_well_formed_co_mk_diverging_trace_to_div_trace (t : stream state) :
 ∀W:well_formed' t.
  ∀H:diverging' t. div_well_formed_co (mk_diverging_trace_to_div_trace' t H) ≝
 match t return λt. well_formed' t → diverging' t → ?
 with
 [ snil ⇒ λ_.λabs. ?
 | scons hd tl ⇒ λW.λH. ? ].
[ cases (?:False) inversion abs #hd #tl #_ #eq destruct
| cases (mk_diverging_trace_to_div_trace_expansion … H) #H' #eq
  lapply (sym_eq ??? … eq) #Req cases Req -Req -eq -H
  cases tl in W H';
  [ #_ #abs cases (?:False) inversion abs #hd #tl #_ #eq destruct
  | -tl #hd2 #tl #W #H
    cases (mk_diverging_trace_to_div_trace_expansion … H) #K #eq >eq
    inversion W [ #s #_ #abs destruct ]
    #hd1' #hd2' #tl' #eq1 #wf #eq2 lapply eq1
    cut (hd=hd1' ∧ hd2 = hd2' ∧ tl=tl') [ cases daemon (* destruct /3/ *) ]
    ** -eq2 ***
    #eq1 %
    [ @step_next //
    | cases daemon (*<eq @div_well_formed_co_mk_diverging_trace_to_div_trace cases daemon (*//*) ]]]
*) qed.

theorem diverging_trace_to_div_trace':
 ∀t: trace'. diverging' t → ∃d: div_trace'.
  head_of_stream … t = Some … (head_of_streamseq … d).
 #t #H %
 [ %{(mk_diverging_trace_to_div_trace' … H)}
   @div_well_formed_co_to_div_well_formed
   @div_well_formed_co_mk_diverging_trace_to_div_trace
   @(well_formed'' t)
 | cases t in H; * normalize // #abs cases (?:False) inversion abs
   [ #s #_ #eq destruct | #hd1 #hd2 #tl #_ #_ #eq destruct ]]
qed.

(* A stream can be extracted from a streamseq using corecursion. *)
let corec stream_of_streamseq (A: Type[0]) (s: streamseq A) : stream A ≝
 match s with [ sscons hd tl ⇒ scons … hd (stream_of_streamseq … tl) ].

(* We need again an expansion lemma to typecheck the proof that the resulting
   stream is divergent. *)
lemma stream_of_streamseq_expansion:
 ∀A,hd,tl.
  stream_of_streamseq A (sscons … hd tl) = scons … hd (stream_of_streamseq … tl).
 #A #hd #tl <(eta_stream … (stream_of_streamseq …)) //
qed.

(* The proof that the resulting stream is diverging also need corecursion.*)
let corec diverging_stream_of_streamseq (s: streamseq state) :
 diverging' (stream_of_streamseq … s) ≝
 match s return λs. diverging' (stream_of_streamseq … s)
 with [ sscons hd tl ⇒ ? ].
 >stream_of_streamseq_expansion % //
qed. 

let corec well_formed_stream_of_streamseq (d: streamseq state) :
 div_well_formed' … d → well_formed' (stream_of_streamseq state d) ≝
 match d
 return λd. div_well_formed' d → ?
 with [ sscons hd1 tl ⇒
  match tl return λtl. div_well_formed' (sscons … tl) → ?
  with [ sscons hd2 tl2 ⇒ λH.? ]].
 >stream_of_streamseq_expansion >stream_of_streamseq_expansion %2
 [2: <stream_of_streamseq_expansion @well_formed_stream_of_streamseq
   #n @(H (S n))
 | @next_step @(H O) ]
qed.

theorem div_trace_to_diverging_trace':
 ∀d: div_trace'. ∃t: trace'. diverging' t ∧
  head_of_stream … t = Some … (head_of_streamseq … d).
 #d %{(mk_trace' (stream_of_streamseq … d) …)}
 [ /2/ | % // cases d * // ]
qed.

(******** How to compare coinductive types *********)

(* Inhabitants of inductive types are compared using Leibniz's equality that,
 on closed terms, coincides with convertibility. Two closed inductive terms
 are equal iff they reduce to the same normal form.
 
 Because of the lazy evaluation of coinductively defined terms, conversion
 does not behave as expected on inhabitants of coinductive types. For example,
 the following two definitions, both in normal form, produce the same
 streamseq 0,1,0,1,… but are not equal because the normal forms are
 syntactically different. *)

let corec zero_one_streamseq1: streamseq ℕ ≝
 sscons … 0 (sscons … 1 zero_one_streamseq1).

let corec one_zero_streamseq: streamseq ℕ ≝
 sscons … 1 (sscons … 0 one_zero_streamseq).

definition zero_one_streamseq2: streamseq ℕ ≝ sscons … 0 one_zero_streamseq. 

(* In place of Leibniz equality, the right notion to compare coinductive terms
 is bisimulation. Two terms t1,t2 are bisimilar if every observation on t1 can
 be performed on t2 as well, and the observed subterms are co-recursively
 bisimilar. In practice two coinductive terms are bisimilar if they are the same
 constructor applied to bisimilar coinductive subterms.
 
 We define bisimilarity for streamseqs using a coinductive predicate. *)
coinductive ss_bisimilar (A: Type[0]) : streamseq A → streamseq A → Prop ≝
 sscons_bisim:
  ∀x,tl1,tl2.
   ss_bisimilar … tl1 tl2 →
    ss_bisimilar … (sscons … x tl1) (sscons … x tl2).

(* The two streams above can be proved to be bisimilar. By using the
 eta_streamseq trick twice, we expand both definitions once so to obtain the
 new proof obligation 0,1,zero_one_streamseq1 = 0,1,zero_one_streamseq2.
 Then we apply twice the sscons_bisim constructor to consume the leading 0 and 1,
 finding again the original goal. Finally we conclude with the coinductive
 hypothesis. The proof is productive because, after the two rewriting, it
 reduces to two applications of the sscons_bisim constructor, immediately
 followed by the recursive call. *)
let corec zero_one_streamseq_eq: ss_bisimilar … zero_one_streamseq1 zero_one_streamseq2 ≝
 ?.
 <(eta_streamseq … zero_one_streamseq1) normalize
 <(eta_streamseq … one_zero_streamseq) normalize
 % % @zero_one_streamseq_eq
qed.

(* We can finally turn streamseqs into a setoid and lift every operation on
 streamseqs to morphisms. We first prove reflexivity, symmetry and transitivity
 of bisimulation because each proof must be given using let corec. *)
let corec reflexive_ss_bisimilar (A: Type[0]): reflexive … (ss_bisimilar A) ≝ ?.
 * #hd #tl % @reflexive_ss_bisimilar
qed.

let corec symmetric_ss_bisimilar (A: Type[0]): symmetric … (ss_bisimilar A) ≝ ?.
 * #hd1 #tl1 * #hd2 #tl2 * #hd #tl1' #tl2' #H % @symmetric_ss_bisimilar @H
qed.

(* In the proof of transitivity we face a technical problem. After inverting one
 of the bisimilarity hypothesis we are left with an equation of the form
 sscons … hd1 tl1 = sscons … hd2 tl2 and we need to extract hd1 = hd2 and
 tl1 = tl2 to conclude the proof. The destruct tactic does exactly this, but
 it produces a proof term that is not recognized to be productive by Matita.
 The trick is to cut the two equalities and to use destruct to prove them.
 In this way the destruct tactic is used only in a side proof inside which there
 is no recursive call, and the whole proof term is recognized to be productive. *)
let corec transitive_ss_bisimilar (A: Type[0]): transitive … (ss_bisimilar A) ≝ ?.
 * #hd1 #tl1 * #hd2 #tl2 * #hd3 #tl3
 * #hd #tl1' #tl2' #H1
 #H inversion H #hd' #tl1'' #tl2'' -H #H #EQ1 #_
 cut (hd=hd' ∧ tl1''=tl2') [ destruct /2/ ] ** #EQ % @transitive_ss_bisimilar //
qed.

definition STREAMSEQ: Type[0] → setoid ≝
 λA.
  mk_setoid (streamseq A)
   (mk_equivalence_relation … (ss_bisimilar A) …).
 //
qed.

unification hint 0 ≔ A:Type[0];
    X ≟ STREAMSEQ A
(* ---------------------------------------- *) ⊢
    streamseq A ≡ carrier X.

(* As an example, we lift streamseq_nth to a morphism. *)
definition STREAMSEQ_NTH: ∀A: Type[0]. STREAMSEQ A ⤞ (LEIBNIZ ℕ) ⤞ (LEIBNIZ A) ≝
 λA. mk_bin_morphism ??? (streamseq_nth A) …. 
 #x1 #x2 #n1 #n2 #bisim * lapply bisim -bisim lapply x2 -x2 lapply x1 -x1 -n2 elim n1
 [ #x1 #x2 #H inversion H //
 | #m #IH #x1 #x2 #H inversion H #hd #tl1 #tl2 #bisim #EQ1 #EQ2 destruct @IH //]
qed.

(* Working with setoids introduce technical complications that one would rather
 avoid. The alternative encoding of streams via sequences doen not solve the
 issue. Sequences are functions and, to capture the mathematical meaning of
 equality for sequences, functions need to be compare using functional
 extensionality. Two functions are extensionally equal when they are pointiwse
 equal, i.e. they map equal inputs to the same outputs. Intensional equality of
 functions, instead, just compares the two codes.
 
 For example, the next two enumerations 0,1,2,… are extensionally, but not
 intensionally equal. *)
definition enum_N1: seq ℕ ≝ λi. i.
definition enum_N2: seq ℕ ≝ λi. i+0.

(* Functional extensionality is defined in the standard library of Matita as
 follows. *)
definition exteqF: ∀A,B:Type[0].∀f,g:A→B.Prop ≝
λA,B.λf,g.∀a.f a = g a.

(* The proof that the two sequences above are extensionally equal is trivial. *)
lemma enum_N_equal: exteqF … enum_N1 enum_N2.
 normalize //
qed.

(* Like for bisimulation, to work sistematically with functional extensionality
 we need to turn the type of sequences into a setoid. The two alternatives are
 actually equivalent with respect to this issue. *)

(******* Generic construction principles *******)

(* When an inductive type is defined Matita automatically
  proves a generic elimination principle using a recursive definition. Later the
  user can apply the generic eliminator in the middle of a proof, without the
  need to make a lemma and prove it using a let rec.
  
  For example, the principle generated for a list is the following:
  
  ∀A:Type[0]. ∀P: A → Prop.
   P (nil …) → (∀hd:A. ∀tl: list A. P tl → P (hd::tl)) →
    ∀l:list A. P l
  
  Here the predicate P is dependent, i.e. it is not just a proposition, but
  a proposition indexed by the list we are analysing.
  
  The corresponding non dependent principle is:
  
  ∀A:Type[0]. ∀P: Prop.
   P → (∀hd:A. ∀tl: list A. P → P) →
    ∀l:list A. P l

  that we can rewrite up to currification as
  
  ∀A:Type[0]. ∀P: Prop.
   ((unit + A × list A × P) → P) →
    list A → P
  
  and, turning the recursor into an iterator, to the simpler form
  
  ∀A:Type[0]. ∀P: Prop.
   ((unit + A × P) → P) →
    list A → P
  
  Thinking of a list as the least fixpoint of the equation

    list A = unit + A × list A

  The above principle says that we can prove P as soon as we can prove P for
  every possible shape of the list, replacing sublists (list A) with the
  result P of recursive calls of the iterator.
  
  Streams are the greatest fixpoint of the same equation
  
    stream A = unit + A × stream A
    
  Dualizing the idea of a generic destructor for list, we obtain the type of the
  generic constructor for streams:
  
  ∀A:Type[0]. ∀P: Prop.
   (P → (unit + A × P)) →
    P → stream A
    
  The above principle says that we can build a stream from a proof of P as soon
  as we can observe from P what shape the stream has and what P will be used to
  generate the reamining of the stream. The principle is indeed easily provable
  in Matita. *)

let corec stream_coind (A: Type[0]) (P: Prop) (H: P → Sum unit (A × P))
 (p:P) : stream A ≝
 match H p with
 [ inl _ ⇒ snil A
 | inr cpl ⇒ let 〈hd,p'〉 ≝ cpl in scons A hd (stream_coind A P H p') ].

(* At the moment Matita does not automatically prove any generic construction
 principle. One reason is that the type of the generated principles is less
 informative than that for elimination principles. The problem is that in the
 type theory of Matita it is not possible to generalize the above type to a
 dependent version, to obtain the exact dual of the elimination principle.
 In case of the elimination principle, the type P depends on the value of the
 input, and the principle proves the dependent product ∀l: list A. P A.
 In the case of the introduction principle, the output is P → list A.
 To obtain a dependent version, we would need a dual of the dependent product
 such that the type of the input is dependent on the value of the output: a
 notion that is not even meaningful when the function is not injective. *)

(* AGGIUNGERE SPIEGAZIONE SU PRODUTTIVITA' *)

(* AGGIUNGERE ESEMPI DI SEMANTICA OPERAZIONE BIG STEP PER LA DIVERGENZA;
   DI PROPRIETA' DI SAFETY;
   DI TOPOLOGIE COINDUTTIVAMENTE GENERATE? *)

(* ################## COME SPIEGARLO QUI? ####################### *)


