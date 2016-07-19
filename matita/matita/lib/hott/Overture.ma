include "hott/types.ma".

(* * * Basic definitions of homotopy type theory, particularly the groupoid structure of identity types. *)

definition relation ≝ λA : Type[0]. A → A → Type[0].

record Reflexive (A) (R : relation A) : Type[0] ≝ {
  reflexivity : ∀x : A. R x x
}.

record Symmetric (A) (R : relation A) : Type[0] ≝ {
  symmetry : ∀x,y. R x y → R y x
}.

record Transitive (A) (R : relation A) : Type[0] ≝ {
  transitivity : ∀x,y,z. R x y → R y z → R x z
}.

(*Tactic Notation "etransitivity" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  refine (@transitivity _ R _ x y z _ _).*)

(*Tactic Notation "etransitivity" := etransitivity _.*)

(* * We would like to redefine [symmetry], which is too smart for its own good, as follows:

<<
Ltac symmetry := refine (@symmetry _ _ _ _ _ _).
>>

But this gives "Error: in Tacinterp.add_tacdef: Reserved Ltac name symmetry.".  This might be fixed with https://coq.inria.fr/bugs/show_bug.cgi?id=3113.  For now, you can [apply symmetry] or [eapply symmetry].  (Note that we can get around this error message by using [Tactic Notation "symmetry"], but, confusingly, this tactic notation never gets called. *)

(* * ** Basic definitions *)

(*CSC: was a Notation in Coq *)
definition idmap : ∀A:Type[0]. A → A ≝ λA,x.x.

(* * Composition of functions. *)
definition compose ≝ λA,B,C: Type[0]. λg : B → C. λf : A → B.
 λx. g (f x).

interpretation "compose" 'compose g f = (compose ??? g f).

(* * ** The groupoid structure of identity types. *)

(* * The results in this file are used everywhere else, so we need to be extra
    careful about how we define and prove things.  We prefer hand-written terms,
    or at least tactics that allow us to retain clear control over the
    proof-term produced. *)

(* * We define our own identity type, rather than using the one in the Coq
     standard library, so as to have more control over transitivity, symmetry
     and inverse.  It seems impossible to change these for the standard
     eq/identity type (or its Type-valued version) because it breaks various
     other standard things.  Merely changing notations also doesn't seem to
     quite work. *)
inductive paths (A : Type[0]) (a : A) : A → Type[0] ≝
  idpath : paths A a a.

interpretation "paths" 'eq t a b = (paths t a b).

(*CSC: MANCANO GLI HINT *)
definition reflexive_paths: ∀A:Type[0]. Reflexive … (paths A) ≝
 λA. mk_Reflexive … (idpath A).

(* * We define equality concatenation by destructing on both its arguments, so
  that it only computes when both arguments are [idpath]. This makes proofs
  more robust and symmetrical. Compare with the definition of [identity_trans]. *)

definition concat : ∀A : Type[0]. ∀x,y,z: A. x = y → y = z → x = z.
 #A #x #y #z #p #q cases q cases p %
qed.

(*CSC: MANCANO GLI HINT *)
definition transitive_paths: ∀A:Type[0]. Transitive … (paths A) ≝
 λA.mk_Transitive … (concat A).

(* * The inverse of a path. *)
definition inverse : ∀A : Type[0]. ∀x,y : A. x = y → y = x.
 #A #x #y * %
qed.

(*CSC: MANCANO GLI HINT *)
definition symmetric_paths: ∀A:Type[0]. Symmetric … (paths A) ≝
 λA. mk_Symmetric … (inverse A).

(* * Note that you can use the built-in Coq tactics [reflexivity] and [transitivity]
    when working with paths, but not [symmetry], because it is too smart for its
    own good.  Instead, you can write [apply symmetry] or [eapply symmetry]. *)

(* * The identity path. *)
interpretation "idpath" 'idpath = (idpath ??).

interpretation "concat" 'append g f = (concat ???? g f). 

interpretation "inverse" 'invert p = (inverse ??? p). 

(* * An important instance of [paths_rect] is that given any dependent type, one
  can _transport_ elements of instances of the type along equalities in the base.

   [transport P p u] transports [u : P x] to [P y] along [p : x = y]. *)
definition transport: ∀A : Type[0]. ∀P: A → Type[0]. ∀x,y : A. x=y → P x → P y.
 #A #P #x #y * //
qed. 

(* * Transport is very common so it is worth introducing a parsing notation for it.
  However, we do not use the notation for output because it hides the fibration,
  and so makes it very hard to read involved transport expression.*)

interpretation "transport" 'transport F p x = (transport ? F ?? p x).

(* * Having defined transport, we can use it to talk about what a homotopy
  theorist might see as "paths in a fibration over paths in the base"; and what
  a type theorist might see as "heterogeneous eqality in a dependent type".
  
  We will first see this appearing in the type of [apD]. *)

(* * Functions act on paths: if [f : A -> B] and [p : x = y] is a path in [A],
     then [ap f p : f x = f y].

   We typically pronounce [ap] as a single syllable, short for "application"; but it may also be considered as an acronym, "action on paths". *)

definition ap: ∀A,B: Type[0]. ∀f:A → B. ∀x,y: A. x = y → f x = f y.
 #A #B #f #x #y * %
qed.

(* * We introduce the convention that [apKN] denotes the application of a K-path
   between functions to an N-path between elements, where a 0-path is simply a
   function or an element. Thus, [ap] is a shorthand for [ap01]. *)
(*CSC: WAS A NOTATION *)
definition ap01 := ap.

definition pointwise_paths:
 ∀A:Type[0]. ∀P:A → Type[0]. ∀f,g: ∀x:A. P x. Type[0] ≝
 λA,P,f,g. ∀x. f x = g x.

interpretation "pointwise_paths" 'congruent f g T = (pointwise_paths ? T f g).

definition apD10: ∀A:Type[0]. ∀B:A→Type[0]. ∀f,g: ∀x. B x. f = g → f ≅ g.
 #A #B #f #g * #x %
qed.

definition ap10: ∀A,B: Type[0]. ∀f,g:A → B. f=g → f ≅ g ≝
 λA,B,f. apD10 … f.

definition ap11: ∀A,B: Type[0]. ∀f,g: A → B. f=g → ∀x,y:A. x=y → f x = g y.
 #A #B #f #g * #x #y * %
qed.

(* * Similarly, dependent functions act on paths; but the type is a bit more
  subtle. If [f : forall a:A, B a] and [p : x = y] is a path in [A], then
  [apD f p] should somehow be a path between [f x : B x] and [f y : B y].
  Since these live in different types, we use transport along [p] to make them
  comparable: [apD f p : p # f x = f y].

  The type [p # f x = f y] can profitably be considered as a heterogeneous or
  dependent equality type, of "paths from [f x] to [f y] over [p]". *)

definition apD:
 ∀A:Type[0]. ∀B:A → Type[0]. ∀f:∀a:A. B a. ∀x,y:A.
   ∀p:x=y. p # (f x) = f y.
 #A #B #f #x #y * %
qed.

(* * ** Equivalences *)

(* * Homotopy equivalences are a central concept in homotopy type theory.
  Before we define equivalences, let us consider when two types [A] and [B]
  should be considered "the same".

  The first option is to require existence of [f : A -> B] and [g : B -> A]
  which are inverses of each other, up to homotopy. Homotopically speaking, we
  should also require a certain condition on these homotopies, which is one of
  the triangle identities for adjunctions in category theory.  Thus, we call
  this notion an *adjoint equivalence*.

  The other triangle identity is provable from the first one, along with all the
  higher coherences, so it is reasonable to only assume one of them.  Moreover,
  as we will see, if we have maps which are inverses up to homotopy, it is always
  possible to make the triangle identity hold by modifying one of the homotopies.

  The second option is to use Vladimir Voevodsky's definition of an equivalence
  as a map whose homotopy fibers are contractible.  We call this notion a
  *homotopy bijection*.

  An interesting third option was suggested by André Joyal: a map [f] which has
  separate left and right homotopy inverses.  We call this notion a
  *homotopy isomorphism*.

  While the second option was the one used originally, and it is the most
  concise one, it makes more sense to use the first one in a formalized
  development, since it exposes most directly equivalence as a structure.
  In particular, it is easier to extract directly from it the data of a homotopy
  inverse to [f], which is what we care about having most in practice.  Thus,
  adjoint equivalences are what we will refer to merely as *equivalences*. *)

(* * Naming convention: we use [equiv] and [Equiv] systematically to denote types
  of equivalences, and [isequiv] and [IsEquiv] systematically to denote the
  assertion that a given map is an equivalence. *)

(* * The fact that [r] is a left inverse of [s]. As a mnemonic, note that the
  partially applied type [Sect s] is the type of proofs that [s] is a section. *)
definition Sect: ∀A,B : Type[0]. (A → B) → (B → A) → Type[0] ≝
 λA,B,s,r. ∀x : A. r (s x) = x.

(* * A typeclass that includes the data making [f] into an adjoint equivalence. *)
record IsEquiv (A,B : Type[0]) (f : A → B) : Type[0] ≝ {
  equiv_inv : B → A ;
  eisretr : Sect … equiv_inv f;
  eissect : Sect … f equiv_inv;
  eisadj : ∀x:A. eisretr (f x) = (* f (equiv_inv (f x)) = f x *) ap … f … (eissect x)
}.

(* * A record that includes all the data of an adjoint equivalence. *)
record Equiv (A,B) : Type[0] ≝ {
  equiv_fun :1> A → B ;
  equiv_isequiv :> IsEquiv … equiv_fun
}.

interpretation "Equiv" 'equiv A B p = (Equiv A B).

(* * A notation for the inverse of an equivalence.  We can apply this to a
  function as long as there is a typeclass instance asserting it to be an
  equivalence.  We can also apply it to an element of [A <~> B], since there is
  an implicit coercion to [A -> B] and also an existing instance of [IsEquiv]. *)

(*CSC: PROBABLY WE NEED TO INTERPRET 'invert_appl TOO *)
interpretation "equiv_inv" 'invert f = (equiv_inv ?? f ?).

(*
(** ** Contractibility and truncation levels *)

(** Truncation measures how complicated a type is.  In this library, a witness that a type is n-truncated is formalized by the [IsTrunc n] typeclass.  In many cases, the typeclass machinery of Coq can automatically infer a witness for a type being n-truncated.  Because [IsTrunc n A] itself has no computational content (that is, all witnesses of n-truncation of a type are provably equal), it does not matter much which witness Coq infers.  Therefore, the primary concerns in making use of the typeclass machinery are coverage (how many goals can be automatically solved) and speed (how long does it take to solve a goal, and how long does it take to error on a goal we cannot automatically solve).  Careful use of typeclass instances and priorities, which determine the order of typeclass resolution, can be used to effectively increase both the coverage and the speed in cases where the goal is solvable.  Unfortunately, typeclass resolution tends to spin for a while before failing unless you're very, very, very careful.  We currently aim to achieve moderate coverage and fast speed in solvable cases.  How long it takes to fail typeclass resolution is not currently considered, though it would be nice someday to be even more careful about things.

In order to achieve moderate coverage and speedy resolution, we currently follow the following principles.  They set up a kind of directed flow of information, intended to prevent cycles and potentially infinite chains, which are often the ways that typeclass resolution gets stuck.

- We prefer to reason about [IsTrunc (S n) A] rather than [IsTrunc n (@paths A a b)].  Whenever we see a statement (or goal) about truncation of paths, we try to turn it into a statement (or goal) about truncation of a (non-[paths]) type.  We do not allow typeclass resolution to go in the reverse direction from [IsTrunc (S n) A] to [forall a b : A, IsTrunc n (a = b)].

- We prefer to reason about syntactically smaller types.  That is, typeclass instances should turn goals of type [IsTrunc n (forall a : A, P a)] into goals of type [forall a : A, IsTrunc n (P a)]; and goals of type [IsTrunc n (A * B)] into the pair of goals of type [IsTrunc n A] and [IsTrunc n B]; rather than the other way around.  Ideally, we would add similar rules to transform hypotheses in the cases where we can do so.  This rule is not always the one we want, but it seems to heuristically capture the shape of most cases that we want the typeclass machinery to automatically infer.  That is, we often want to infer [IsTrunc n (A * B)] from [IsTrunc n A] and [IsTrunc n B], but we (probably) don't often need to do other simple things with [IsTrunc n (A * B)] which are broken by that reduction.
*)

(** *** Contractibility *)

(** A space [A] is contractible if there is a point [x : A] and a (pointwise) homotopy connecting the identity on [A] to the constant map at [x].  Thus an element of [contr A] is a pair whose first component is a point [x] and the second component is a pointwise retraction of [A] to [x]. *)

(** We use the [Contr_internal] record so as not to pollute typeclass search; we only do truncation typeclass search on the [IsTrunc] datatype, usually.  We will define a notation [Contr] which is equivalent to [Contr_internal], but picked up by typeclass search.  However, we must make [Contr_internal] a class so that we pick up typeclasses on [center] and [contr].  However, the only typeclass rule we register is the one that turns it into a [Contr]/[IsTrunc].  Unfortunately, this means that declaring an instance like [Instance contr_foo : Contr foo := { center := bar }.] will fail with mismatched instances/contexts.  Instead, we must iota expand such definitions to get around Coq's deficiencies, and write [Instance contr_foo : Contr foo := let x := {| center := bar |} in x.] *)
Class Contr_internal (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Arguments center A {_}.

(** *** Truncation levels *)

(** Truncation measures how complicated a type is in terms of higher path spaces. The (-2)-truncated types are the contractible ones, whose homotopy is completely trivial. The (n+1)-truncated types are those whose path spaces are n-truncated.

   Thus, (-1)-truncated means "the space of paths between any two points is contactible". Such a space is necessarily a sub-singleton: any two points are connected by a path which is unique up to homotopy. In other words, (-1)-truncated spaces are truth values (we call them "propositions").

   Next, 0-truncated means "the space of paths between any two points is a sub-singleton". Thus, two points might not have any paths between them, or they have a unique path. Such a space may have many points but it is discrete in the sense that all paths are trivial. We call such spaces "sets".
*)

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

(** We will use [Notation] for [trunc_index]es, so define a scope for them here. *)
Delimit Scope trunc_scope with trunc.
Bind Scope trunc_scope with trunc_index.
Arguments trunc_S _%trunc_scope.

Fixpoint nat_to_trunc_index (n : nat) : trunc_index
  := match n with
       | 0 => trunc_S (trunc_S minus_two)
       | S n' => trunc_S (nat_to_trunc_index n')
     end.

Coercion nat_to_trunc_index : nat >-> trunc_index.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Notation minus_one:=(trunc_S minus_two).
(** Include the basic numerals, so we don't need to go through the coercion from [nat], and so that we get the right binding with [trunc_scope]. *)
Notation "0" := (trunc_S minus_one) : trunc_scope.
Notation "1" := (trunc_S 0) : trunc_scope.
Notation "2" := (trunc_S 1) : trunc_scope.

Arguments IsTrunc_internal n A : simpl nomatch.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

(** We use the priciple that we should always be doing typeclass resolution on truncation of non-equality types.  We try to change the hypotheses and goals so that they never mention something like [IsTrunc n (_ = _)] and instead say [IsTrunc (S n) _].  If you're evil enough that some of your paths [a = b] are n-truncated, but others are not, then you'll have to either reason manually or add some (local) hints with higher priority than the hint below, or generalize your equality type so that it's not a path anymore. *)

Typeclasses Opaque IsTrunc. (* don't auto-unfold [IsTrunc] in typeclass search *)

Arguments IsTrunc : simpl never. (* don't auto-unfold [IsTrunc] with [simpl] *)

Instance istrunc_paths (A : Type) n `{H : IsTrunc (trunc_S n) A} (x y : A)
: IsTrunc n (x = y)
  := H x y. (* but do fold [IsTrunc] *)

Hint Extern 0 => progress change IsTrunc_internal with IsTrunc in * : typeclass_instances. (* Also fold [IsTrunc_internal] *)

(** Picking up the [forall x y, IsTrunc n (x = y)] instances in the hypotheses is much tricker.  We could do something evil where we declare an empty typeclass like [IsTruncSimplification] and use the typeclass as a proxy for allowing typeclass machinery to factor nested [forall]s into the [IsTrunc] via backward reasoning on the type of the hypothesis... but, that's rather complicated, so we instead explicitly list out a few common cases.  It should be clear how to extend the pattern. *)
Hint Extern 10 =>
progress match goal with
           | [ H : forall x y : ?T, IsTrunc ?n (x = y) |- _ ]
             => change (IsTrunc (trunc_S n) T) in H
           | [ H : forall (a : ?A) (x y : @?T a), IsTrunc ?n (x = y) |- _ ]
             => change (forall a : A, IsTrunc (trunc_S n) (T a)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (x y : @?T a b), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a), IsTrunc (trunc_S n) (T a b)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (c : @?C a b) (x y : @?T a b c), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a) (c : C a b), IsTrunc (trunc_S n) (T a b c)) in H; cbv beta in H
           | [ H : forall (a : ?A) (b : @?B a) (c : @?C a b) (d : @?D a b c) (x y : @?T a b c d), IsTrunc ?n (x = y) |- _ ]
             => change (forall (a : A) (b : B a) (c : C a b) (d : D a b c), IsTrunc (trunc_S n) (T a b c d)) in H; cbv beta in H
         end.

Notation Contr := (IsTrunc minus_two).
Notation IsHProp := (IsTrunc minus_one).
Notation IsHSet := (IsTrunc 0).

Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.

(** *** Function extensionality *)

(** The function extensionality axiom is formulated as a class. To use it in a theorem, just assume it with [`{Funext}], and then you can use [path_forall], defined below.  If you need function extensionality for a whole development, you can assume it for an entire Section with [Context `{Funext}].  *)
Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g
  :=
  (@apD10 A P f g)^-1.

Definition path_forall2 `{Funext} {A B : Type} {P : A -> B -> Type} (f g : forall x y, P x y) :
  (forall x y, f x y = g x y) -> f = g
  :=
  (fun E => path_forall f g (fun x => path_forall (f x) (g x) (E x))).


(** *** Tactics *)

(** We declare some more [Hint Resolve] hints, now in the "hint database" [path_hints].  In general various hints (resolve, rewrite, unfold hints) can be grouped into "databases". This is necessary as sometimes different kinds of hints cannot be mixed, for example because they would cause a combinatorial explosion or rewriting cycles.

   A specific [Hint Resolve] database [db] can be used with [auto with db].

   The hints in [path_hints] are designed to push concatenation *outwards*, eliminate identities and inverses, and associate to the left as far as  possible. *)

(** TODO: think more carefully about this.  Perhaps associating to the right would be more convenient? *)
Hint Resolve
  @idpath @inverse
 : path_hints.

Hint Resolve @idpath : core.

Ltac path_via mid :=
  apply @concat with (y := mid); auto with path_hints.

(** We put [Empty] here, instead of in [Empty.v], because [Ltac done] uses it. *)
Inductive Empty : Type := .

Definition not (A:Type) : Type := A -> Empty.
Notation "~ x" := (not x) : type_scope.
Hint Unfold not: core.

(** *** Pointed types *)

(** A space is pointed if that space has a point. *)
Class IsPointed (A : Type) := point : A.
Definition pointedType := { u : Type & IsPointed u }.

(** Ssreflect tactics, adapted by Robbert Krebbers *)
Ltac done :=
  trivial; intros; solve
    [ repeat first
      [ solve [trivial]
      | solve [eapply symmetry; trivial]
      | reflexivity
      (* Discriminate should be here, but it doesn't work yet *)
      (* | discriminate *)
      | contradiction
      | split ]
    | match goal with
      H : ~ _ |- _ => solve [destruct H; trivial]
      end ].
Tactic Notation "by" tactic(tac) :=
  tac; done.

(** A convenient tactic for using function extensionality. *)
Ltac by_extensionality x :=
  intros; unfold compose;
  match goal with
  | [ |- ?f = ?g ] => eapply path_forall; intro x;
      match goal with
        | [ |- forall (_ : prod _ _), _ ] => intros [? ?]
        | [ |- forall (_ : sigT _ _), _ ] => intros [? ?]
        | _ => intros
    end;
    simpl; auto with path_hints
  end.

(** Removed auto. We can write "by (path_induction;auto with path_hints)"
 if we want to.*)
Ltac path_induction :=
  intros; repeat progress (
    match goal with
      | [ p : _ = _  |- _ ] => induction p
      | _ => idtac
    end
  ).

(** The tactic [f_ap] is a replacement for the previously existing standard library tactic [f_equal].  This tactic works by repeatedly applying the fact that [f = g -> x = y -> f x = g y] to turn, e.g., [f x y = f z w] first into [f x = f z] and [y = w], and then turns the first of these into [f = f] and [x = z].  The [done] tactic is used to detect the [f = f] case and finish, and the [trivial] is used to solve, e.g., [x = x] when using [f_ap] on [f y x = f z x].  This tactic only works for non-dependently-typed functions; we cannot express [y = w] in the first example if [y] and [w] have different types.  If and when Arnaud's new-tacticals branch lands, and we can have a goal which depends on the term used to discharge another goal, then this tactic should probably be generalized to deal with dependent functions. *)
Ltac f_ap :=
  lazymatch goal with
    | [ |- ?f ?x = ?g ?x ] => apply (@apD10 _ _ f g);
                             try (done || f_ap)
    | _ => apply ap11;
          [ done || f_ap
          | trivial ]
  end.

(** [expand] replaces both terms of an equality (either [paths] or [pointwise_paths] in the goal with their head normal forms *)
Ltac expand :=
  match goal with
    | [ |- ?X = ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' = Y')
    | [ |- ?X == ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' == Y')
  end; simpl.

(** [atomic x] is the same as [idtac] if [x] is a variable or hypothesis, but is [fail 0] if [x] has internal structure. *)
Ltac atomic x :=
  match x with
    | ?f _ => fail 1 x "is not atomic"
    | (fun _ => _) => fail 1 x "is not atomic"
    | forall _, _ => fail 1 x "is not atomic"
    | _ => idtac
  end.
*)
