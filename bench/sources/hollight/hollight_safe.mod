infixl ' 139.

{ /***** Trusted code base *******/

/* Trusted library functions:
 * append
 * fold2_append
 * put_binds
*/

local thm, provable, def0, term, term', typ, loop, prove, saved, check1,
 toplevel_loop, toplevel.

proves T TY :- provable T TY.

typ bool.
typ ind.

/*term T TY :- $print (term T TY), fail.*/
term T TY :- $is_flex T, !.%, $delay (term T TY) [ T ].
term T TY :- term' T TY.
term' (lam F) (arr A B) :- pi x\ term' x A => term (F x) B.
term' (F ' T) B :- term F (arr A B), term T A.
term' eq (arr A (arr A bool)).

/*propagate [ (G1 ?- term (X @ L1) TY1) ] [ (G2 ?- term (X @ L2) TY2) ] NEW :-
 list_map L1 (x\ y\ (term x y ; y = xxx)) LTY1,
 list_map L2 (x\ y\ (term x y ; y = xxx)) LTY2,
 NEW = (TY1 = TY2, LTY1 = LTY2).*/

/*propagate [ (G ?- term (X @ L) TY) ] [ (G ?- term (X @ L) TY) ] true .*/

% thm : bounded tactic -> bounded sequent -> list (bounded sequent) -> o
thm C (seq Gamma G) _ :- debug, $print Gamma "|- " G " := " C, fail.

/* << HACKS FOR DEBUGGING */
term' p bool.
term' q bool.
term' f (arr bool bool).
term' (g X) bool :- term X bool.
term' c bool.

thm daemon (seq Gamma F) [].
/* >> HACKS FOR DEBUGGING */

thm r (seq Gamma (eq ' X ' X)) [].
thm (t Y) (seq Gamma (eq ' X ' Z))
 [ seq Gamma (eq ' X ' Y), seq Gamma (eq ' Y ' Z) ] :- term X A, term Y A.
thm (m P) (seq Gamma Q) [ seq Gamma (eq ' P ' Q), seq Gamma P ] :- term P bool.
thm b (seq Gamma (eq ' ((lam F) ' X) ' (F X))) [].
thm c (seq Gamma (eq ' (F ' X) ' (G ' Y)))
 [ seq Gamma (eq ' F ' G) , seq Gamma (eq ' X ' Y) ] :- term X A, term Y A.
thm k (seq Gamma (eq ' (lam S) ' (lam T)))
 [ bind A x \  seq Gamma (eq ' (S x) ' (T x)) ] :- term (lam S) (arr A _).
thm s (seq Gamma (eq ' P ' Q)) [ seq (P :: Gamma) Q, seq (Q :: Gamma) P ] :-
 term P bool.
thm (h IGN) (seq Gamma P) [] :- append IGN [ P | Gamma2 ] Gamma.

thm d (seq Gamma (eq ' C ' A)) [] :- def0 C A.
thm (th NAME) (seq _ G) [] :- provable NAME G.

thm (thenll TAC1 TACN) SEQ SEQS :-
 thm TAC1 SEQ NEW,
 deftacl TACN NEW TACL,
 fold2_append TACL NEW thm SEQS.

/*debprint _ (then _ _) :- !.
debprint _ (thenl _ _) :- !.
debprint O T :- $print O T.*/

thm TAC SEQ SEQS :-
 deftac TAC SEQ XTAC,
 /*debprint "<<" TAC,
 (*/ thm XTAC SEQ SEQS /*, debprint ">>" TAC
 ; debprint "XX" TAC, fail)*/.

thm (! TAC) SEQ SEQS :-
 thm TAC SEQ SEQS,
 !.

thm id SEQ [ SEQ ].

thm (w Gamma1) (seq Gamma F) [ seq WGamma F ] :-
 append Gamma1 [ P | Gamma2 ] Gamma,
 append Gamma1 Gamma2 WGamma.

thm (bind A TAC) (bind A SEQ) NEWL :-
 pi x \ term' x A => thm (TAC x) (SEQ x) (NEW x), put_binds (NEW x) x A NEWL.

thm ww (bind A x \ SEQ) [ SEQ ].

/* debuggin only, remove it */
%thm A B C :- $print "FAILED " (thm A B C), fail.

% loop : bool -> list (bounded sequent) -> list (bounded tactics) -> o
%loop INTERACTIVE SEQS TACS :- $print "LOOP" (loop INTERACTIVE SEQS TACS), fail.
loop _ [] [].
loop INTERACTIVE [ SEQ | OLD ] [ TAC | OTHER_TACS ] :-
 (INTERACTIVE = true, !,
   $print,
   list_iter_rev [ SEQ | OLD ] print_sequent,
   read_in_context SEQ ITAC
 ; ITAC = TAC),
 ( thm ITAC SEQ NEW,
   append NEW OLD SEQS,
   (INTERACTIVE = true, !,
    mk_script ITAC NEW NEW_TACS TAC,
    append NEW_TACS OTHER_TACS TACS
   ; TACS = OTHER_TACS ),
   loop INTERACTIVE SEQS TACS
 ; (INTERACTIVE = true, !, $print "error" ;
    $print "aborted", halt),
   loop INTERACTIVE [ SEQ | OLD ] [ TAC | OTHER_TACS ] ).
%loop INTERACTIVE SEQS TACS :- $print "FAIL" (loop INTERACTIVE SEQS TACS), fail.

prove G TACS :-
 term G bool,
 loop true [ seq [] G ] TACS,
 $print "proof completed".

saved G TACS :-
 term G bool,
 loop false [ seq [] G ] TACS.

/* check1 I O
   checks the declaration I
   returns the new assumption O */
check1 (pi C) (pi O) :- pi x \ check1 (C x) (O x).
check1 (theorem NAME GOAL TACTICS) (provable NAME GOAL) :-
  not (provable NAME _),
  saved GOAL TACTICS,
  $print NAME ":" GOAL,
  !.
check1 (new_basic_type TYPE REP ABS REPABS ABSREP P TACTICS) HYPS :-
  not (typ TYPE),
  not (term REP _),
  not (term ABS _),
  not (term ABSREP _),
  not (term REPABS _),
  term P (arr X bool),
  saved (exists ' P ) TACTICS,
  REPTYP = (arr TYPE X),
  ABSTYP = (arr X TYPE),
  ABSREPTYP = (forall ' lam x \ eq ' (abs ' (rep ' x)) ' x),
  REPABSTYP = (forall ' lam x \ eq ' (P ' x) ' (eq ' (rep ' (abs ' x)) x)),
  $print new typ TYPE,
  $print REP ":" REPTYP,
  $print ABS ":" ABSTYP,
  $print ABSREP ":" ABSREPTYP,
  $print REPABS ":" REPABSTYP,
  !,
  HYPS =
   ( typ TYPE
   , term' REP REPTYP
   , term' ABS ABSTYP
   , provable ABSREP ABSREPTYP
   , provable REPABS REPABSTYP
   ).
check1 (def NAME TYP DEF) HYPS :-
  not (def0 NAME _),
  term DEF TYP, /* TODO: INFER TYP AUTOMATICALLY */
  $print NAME ":" TYP,
  $print NAME "=" DEF,
  HYPS = (def0 NAME DEF, term' NAME TYP).

check [] :- toplevel.
check [ C | NEXT ] :- check1 C H, H => check NEXT.

toplevel_loop :-
 $print "Enter a statement to prove or stop to stop",
 read G,
 ( G = stop, !
 ; prove G [ TAC ],
   !,
   canonical TAC CANONICALTAC,
   $print "Enter the theorem name",
   read NAME,
   $print (theorem NAME G [ CANONICALTAC ]),
   provable NAME G => toplevel_loop
 ; $print "Bad statement " G,
   toplevel_loop).

toplevel :-
 $print "Welcome to HOL extra-light",
 toplevel_loop.

}

/************ interactive and non interactive loops ********/

mk_script (bind A T) NEW NEW_TACS (bind A T2) :- !,
 pi x \
  put_binds (NEW2 x) x A NEW,
  mk_script (T x) (NEW2 x) (NEWT x) (T2 x),
  put_binds (NEWT x) x A NEW_TACS.
mk_script ITAC NEW NEW_TACS (thenl ITAC NEW_TACS) :-
 mk_list_of_bounded_fresh NEW NEW_TACS.

read_in_context (bind A K) (bind A TAC) :-
 pi x \ term' x A => read_in_context (K x) (TAC x).
read_in_context (seq A B) TAC :- read TAC, (TAC = backtrack, !, fail ; TAC = toplevel, !, toplevel ; true).

print_sequent (seq Gamma G) :- $print Gamma "|-" G.
print_sequent (bind A F) :- pi x \ print_sequent (F x).

/* turns thenl into then */
canonical (bind A T1) (bind A T2) :- !,
 pi x \ canonical (T1 x) (T2 x).
canonical (thenl T L) OTAC :- !,
 list_map L canonical L2,
 (mk_constant_list L2 S L2, !,
  (S = [], !, OTAC = T ; OTAC = then T S)
 ; OTAC = thenl T L2).
canonical T T.

/************ library of basic data types ********/
/* bounded 'a ::= 'a | bind A (F : _ -> bounded 'a) */

% put_binds : list 'b -> 'a -> 'c -> list (bounded 'b) -> o
% put_binds [ f1,...,fn ] x t [ bind t x \ f1,...,bind t x fn ]
% binding all the xs that occur in f1,...,fn
%put_binds A B C D :- $print "PUT BINDS" (put_binds A B C D), fail.
put_binds [] _ _ [].
put_binds [ YX | YSX ] X A [ bind A Y | YYS ] :-
 YX = Y X, put_binds YSX X A YYS.
%put_binds A B C D :- $print "KO PUT BINDS" (put_binds A B C D), fail.

mk_bounded_fresh (bind _ F) (bind _ G) :- !, pi x\ mk_bounded_fresh (F x) (G x).
mk_bounded_fresh _ X.

mk_list_of_bounded_fresh [] [].
mk_list_of_bounded_fresh [S|L] [X|R] :-
 mk_bounded_fresh S X, mk_list_of_bounded_fresh L R.

/* list functions */

append [] L L.
append [ X | XS ] L [ X | RES ] :- append XS L RES.

fold2_append [] [] _ [].
fold2_append [ X | XS ] [ Y | YS ] F OUTS :-
 F X Y OUT, fold2_append XS YS F OUTS2, append OUT OUTS2 OUTS.

list_map [] _ [].
list_map [X|XS] F [Y|YS] :- F X Y, list_map XS F YS.

list_iter_rev [] _.
list_iter_rev [X|XS] F :- list_iter_rev XS F, F X.

mem [ X | _ ] X, !.
mem [ _ | XS ] X :- mem XS X.

mk_constant_list [] _ [].
mk_constant_list [_|L] X [X|R] :- mk_constant_list L X R.

/********** tacticals ********/

/*sigma ff \*/ deftac fail SEQ ff.

deftacl (constant_tacl TACL) SEQS TACL.

deftac (thenl TAC TACL) SEQ XTAC :-
 XTAC = thenll TAC (constant_tacl TACL).

deftacl (all_equals_list TAC2) SEQS TACL :-
 mk_constant_list SEQS TAC2 TACL.

deftac (then TAC1 TAC2) SEQ XTAC :-
 XTAC = thenll TAC1 (all_equals_list TAC2).

deftac (then! TAC1 TAC2) _ (then (! TAC1) TAC2).

deftac (orelse TAC1 TAC2) SEQ XTAC :-
 XTAC = TAC1 ; XTAC = TAC2.

deftac (orelse! TAC1 TAC2) _ (orelse (! TAC1) TAC2).

deftac (bind* TAC) SEQ (orelse! (bind _ x \ bind* TAC) TAC).

deftac (repeat TAC) SEQ XTAC :-
 ( XTAC = then TAC (repeat (bind* TAC))
 ; XTAC = id).

deftac (repeat! TAC) SEQ (orelse! (then! TAC (repeat! (bind* TAC))) id).

deftac (printtac TAC) SEQ TAC :-
 $print "SEQ" SEQ ":=" TAC.

deftac (time TAC) SEQ XTAC :-
 $gettimeofday B,
 XTAC = thenll TAC (time_after TAC B).

deftacl (time_after TAC B) SEQS TACL :-
 $gettimeofday A,
 D is A - B,
 mk_constant_list SEQS id TACL,
 $print "TIME SPENT " D "FOR" TAC.

/********** tactics ********/

deftac (w G) (seq Gamma _) (w Gamma1) :-
 append Gamma1 [ G | _ ] Gamma.

deftac h SEQ (h L).

/*** eq ***/

deftac sym (seq Gamma (eq ' L ' R)) TAC :-
 TAC = thenl (m (eq ' R ' R)) [ thenl c [ thenl c [ r , id ] , r ] , r ].

deftac eq_true_intro (seq Gamma (eq ' P ' tt)) TAC :-
 TAC = thenl s [ th tt_intro, w [] ].

/*** true ***/

/*** and ***/

deftac conj (seq Gamma (and ' P ' Q)) TAC :-
 TAC =
  then
   (then (conv dd)
     (then k (bind _ x \
       thenl c
        [ thenl c [ r, eq_true_intro ] ,
          eq_true_intro ])))
   ww.

/* Gamma  "|-"  q    --->   Gamma "|-" and ' p ' q*/
deftac (andr P) (seq Gamma Q) TAC :-
 TAC =
  (thenl (m ((lam f \ f ' P ' Q) ' (lam x \ lam y \ y)))
    [ then
       %(repeat (conv (depth_tac b))) ROBUS VERSION LINE BELOW
       (then (conv (land_tac b)) (then (conv (land_tac (rator_tac b))) (conv (land_tac b))))
      r
    , thenl (conv (rator_tac id))
       [ then (thenl (t (lam f \ f ' tt ' tt)) [ id, r ])
          (thenl (m (and ' P ' Q)) [ dd , id ])
       , then (repeat (conv (depth_tac b))) (th tt_intro) ]]).

/* (and ' p ' q) :: nil  "|-"  q */
deftac andr (seq Gamma Q) TAC :-
 mem Gamma (and ' P ' Q),
 TAC = then (andr P) h.

/* Gamma  "|-"  p    --->   Gamma "|-" and ' p ' q*/
deftac (andl Q) (seq Gamma P) TAC :-
 TAC =
  (thenl (m ((lam f \ f ' P ' Q) ' (lam x \ lam y \ x)))
    [ then
       %(repeat (conv (depth_tac b))) ROBUS VERSION LINE BELOW
       (then (conv (land_tac b)) (then (conv (land_tac (rator_tac b))) (conv (land_tac b))))
      r
    , thenl (conv (rator_tac id))
       [ then (thenl (t (lam f \ f ' tt ' tt)) [ id, r ])
          (thenl (m (and ' P ' Q)) [ dd , id ])
       , then (repeat (conv (depth_tac b))) (th tt_intro) ]]).

/* (and ' p ' q) :: nil  "|-"  p */
deftac andl (seq Gamma P) TAC :-
 mem Gamma (and ' P ' Q),
 TAC = then (andl Q) h.


/*** forall ***/

/* |- forall ' F  -->   |- F ' x */
deftac forall_i (seq Gamma (forall ' lam G)) TAC :-
 TAC = then (conv dd) (then k (bind _ x \ eq_true_intro)).

/* forall ' F |- F ' T */
deftac forall_e (seq Gamma GX) TAC :-
 mem Gamma (forall ' (lam G)), GX = G X,
 TAC = thenl (m ((lam G) ' X)) [ b, thenl (m ((lam z \ tt) ' X))
  [ thenl c [ then sym (thenl (m (forall ' lam G)) [dd,h ]), r ]
  , then (conv b) (th tt_intro) ] ].

/* forall ' F |- f  -->  F ' a, forall ' F |- f */
deftac (lforall F A) (seq Gamma G) TAC :-
 TAC = thenl (m (impl ' (F A) ' G))
  [ thenl s [ then mp forall_e, then i h ] , then (w (forall ' lam F)) i ].

/* forall ' F |- f  -->  F ' a, forall ' F |- f */
deftac (lforall A) (seq Gamma G) (lforall F A) :-
 mem Gamma (forall ' lam F).

/* forall ' F |- f  -->  F ' a, forall ' F |- f */
deftac lforall (seq Gamma G) (lforall A).

/* forall ' F |- f  -->  F ' a, forall ' F |- f */
deftac (lforall_last A) (seq ((forall ' lam F)::Gamma) G) (lforall F A).

/*** false ***/
              
/*** impl ***/

/* |- p=>q  -->  p |- q */
deftac i (seq Gamma (impl ' P ' Q)) TAC :-
 TAC = then (conv dd) (thenl s [ andl, thenl conj [ h [], id ]]).

/* p=>q |- q  -->  |- p */
deftac (mp P) (seq Gamma Q) TAC :-
 TAC = then (andr P) (thenl (m P) [ then sym (thenl (m (impl ' P ' Q)) [ dd , h ]) , id ]).

/* p=>q |- q  -->  |- p */
deftac mp (seq Gamma Q) (mp P) :-
 mem Gamma (impl ' P ' Q).

/* |- q   -->   p |- q  and  |- p */
deftac (cut P) (seq Gamma Q) TAC :-
 TAC = then (andr P) (thenl (m P) [then sym (thenl (m (impl ' P ' Q)) [then (conv (land_tac dd)) r, i] ) , id]). 

/* |-q  --> p |- q   where the theorem T proves p */
deftac (cutth T) SEQ TAC :-
 proves T X,
 TAC = (thenl (cut X) [ id, th T ]).

/* applies the theorem T */
deftac (applyth T) SEQ (then (cutth T) apply_last).

/* impl p q, Gamma |- f   --->   /*impl q f*/ Gamma |- p  ,  q, Gamma |- f */
deftac (lapply P Q) (seq Gamma F) TAC :-
 TAC =
  thenl (m (impl ' Q ' F)) [ thenl s [ then (mp Q) (then (w (impl ' Q ' F)) (then (mp P) (w (impl ' P ' Q)))) , then i (h [A]) ] , then (w (impl ' P ' Q)) (then i id) ].

/* For debugging only (?) For capturing metavariables */
deftac (inspect SEQ TAC) SEQ TAC.

/* impl p q, Gamma |- f   --->   /*impl q f*/ Gamma |- p  ,  q, Gamma |- f */
deftac lapply (seq Gamma F) (lapply P Q) :-
 mem Gamma (impl ' P ' Q).

/* impl p q, Gamma |- f   --->   /*impl q f*/ Gamma |- p  ,  q, Gamma |- f */
deftac lapply_last (seq ((impl ' P ' Q)::Gamma) F) (lapply P Q).

/*** not ***/

/*** exists ***/

/**** apply, i.e. forall + impl ****/

deftac (apply X) SEQ h :- $is_flex X, !.

deftac (apply X) SEQ h.

deftac (apply (impl ' P ' Q)) SEQ TAC :-
 TAC = thenl (lapply P Q) [ id, apply_last ].

deftac (apply (forall ' lam G)) SEQ TAC :-
 TAC = then (lforall G X) apply_last.

deftac apply_last (seq (H::Gamma) F) (apply H).

deftac apply (seq Gamma F) (apply H) :-
 mem Gamma H.

/********** conversion(als) ***********/

/* expands definitions, even if applied to arguments */
deftac dd (seq _ (eq ' T ' X)) d.
deftac dd (seq _ (eq ' (D ' T) ' X))
 (thenl  (t A) [thenl c [dd , r], b]).

/* folds a definition, even if applied to arguments */
/* BUG: it seems to fail with restriction errors in some cases */
deftac f SEQ (then sym dd).

deftac (rand_tac C) SEQ TAC :-
  TAC = thenl c [ r , C ].

deftac (rator_tac C) SEQ TAC :-
  TAC = thenl c [ C , r ].

deftac (abs_tac C) SEQ TAC :-
  TAC = then k (bind A x \ C).

deftac (land_tac C) SEQ TAC :-
  TAC = thenl c [ thenl c [ r, C ] , r ].

deftac (sub_tac C) SEQ TAC :-
  TAC = orelse (rand_tac C) (orelse (rator_tac C) (abs_tac C)).

deftac (try TAC) SEQ (orelse TAC id).

deftac (depth_tac C) SEQ TAC :-
  TAC = then (try C) (sub_tac (depth_tac C)).

deftac (conv C) (seq Gamma F) TAC :-
 TAC = thenl (m G) [ then sym C , id ].

/********** Automation ***********/
/* TODO:
 1) left rule for = (in the sense of coimplication) missing
 2) our lforall gets rid of the hypothesis (bad) */
/* left tries to reduce the search space via focusing */
deftac left (seq Gamma _) TAC :-
 mem Gamma (not ' F),
 TAC =
  (!
   (then (cutth not_e)
    (then (lforall_last F)
     (thenl lapply [ h, (w (not ' F)) ])))).
deftac left (seq Gamma _) TAC :-
 /* A bit long because we want to beta-reduce the produced hypothesis.
    Maybe this should be automatized somewhere else. */
 mem Gamma (exists ' F),
 TAC =
  (!
   (then (cutth exists_e)
    (then (lforall_last F)
     (thenl lapply [ h, then (w (exists ' F)) (then apply_last (then forall_i (bind _ x \ then (try (conv (land_tac b))) i))) ])))).
deftac left (seq Gamma H) TAC :-
 mem Gamma (or ' F ' G),
 TAC =
  (!
   (then (cutth or_e)
    (then (lforall_last F)
     (then (lforall_last G)
      (then (lforall_last H)
       (thenl lapply [ h, then (w (or ' F ' G)) (then apply_last i)])))))).
deftac left (seq Gamma H) TAC :-
 mem Gamma (and ' F ' G),
 TAC =
  (!
   (then (cutth and_e)
    (then (lforall_last F)
     (then (lforall_last G)
      (then (lforall_last H)
       (thenl lapply [ h, then (w (and ' F ' G)) (then apply_last (then i i))])))))).

deftac not_i (seq _ (not ' _)) (applyth not_i).

deftac inv _ TAC :-
 TAC =
 (then!
  (repeat!
   (orelse! conj (orelse! forall_i (orelse! i (orelse! not_i s)))))
  (bind* (repeat! left))).

deftac (sync N) (seq _ tt) (th tt_intro).
deftac (sync N) (seq Gamma _) (then (applyth ff_elim) h) :-
 mem Gamma ff.
deftac (sync N) (seq _ (or ' _ ' _))
 (orelse (then (applyth orr) (itaut N)) (then (applyth orl) (itaut N))).
deftac (sync N) (seq _ (exists ' _)) (then (applyth exists_i) (itaut N2)) :-
 N2 is N - 2.
deftac (itaut N) SEQ fail :- N =< 0, !.
deftac (itaut N) SEQ TAC :-
 %$print (itaut N) SEQ,
 N1 is N - 1,
 N2 is N - 2,
 TAC =
 (then! inv
  (bind*
   (orelse h
   (orelse (sync N)
   (orelse /* Hypothesis not moved to front */ (then lforall (itaut N2))
   (then lapply (itaut N1))))))).

/********** inductive things

defined in terms of new_type_definition
let nat_induct, nat_recurs = define_type "nat = O | S nat"

val nat_induct : !P. P O /\ ....
val nat_recurs : !f0 f1. ?f. f O = f0 /\ ...

term O nat
term S (arr nat nat)

injectivity nat
distinctiness nat
cases nat

smart way to instantiate nat_recurs
let plus = new_recursive_definition nat_RECUR
 "!n. plus O n = n /\ (!m n. plus (S m) n = S (plus m n)"
val plus : (!n. plus 0 n = n) /\ ....

every time you introduce a type you need to prove a theorem:
 example, to define even numbers out of natural numbers you prove
 ?n. EVEN n

you obtain natural numbers from the axiom
INFINITY_AX: ?f : ind -> ind. ONE_ONE f /\ -ONTO f

e.g. IND_SUC_0_EXISTS
?(f: ind -> ind) z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\ (!x. ~(f x = z))

then use new_definition with
IND_SUC = @(f: ind -> ind). ?z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\ (!x. ~(f x = z))
IND_0 = @z:ind. (!x1 x2. (IND_SUC x1 = IND_SUC x2) = (x1 = x2)) /\ (!x. ~(IND_SUC x = z))

and then your define the natural numbers

in the kernel two types: bool and ind (the type of individuals)

INFINITY_AX, SELECT_AX (* axiom of choice *), ETA_AX

*******/

/********** the library ********/

main :-
 check
  [ /*********** Connectives and quantifiers ********/
    def tt bool
     (eq ' (lam x\ x) ' (lam x\ x))
  , (pi A \ def forall (arr (arr A bool) bool)
     (lam f \ eq ' f ' (lam g \ tt)))
  , def ff bool
     (forall ' lam x \ x)
  , def and
     (arr bool (arr bool bool))
     (lam x \ lam y \ eq ' (lam f \ f ' x ' y) ' (lam f \ f ' tt ' tt))
  , def impl (arr bool (arr bool bool))
     (lam a \ lam b \ eq ' (and ' a ' b) ' a)
  , (pi A \ def exists (arr (arr A bool) bool)
     (lam f \ forall ' (lam c \ (impl ' (forall ' (lam a \ (impl ' (f ' a) ' c))) ' c))))
  , def not (arr bool bool)
     (lam x \ impl ' x ' ff)
  , def or (arr bool (arr bool bool))
     (lam x \ lam y \ forall ' lam c \ impl ' (impl ' x ' c) ' (impl ' (impl ' y ' c) ' c))
  , theorem tt_intro tt [then (conv dd) (then k (bind _ x12 \ r))]
  , theorem ff_elim (forall ' (lam x2 \ impl ' ff ' x2))
     [then forall_i (bind bool x3\ then (conv (land_tac dd)) (then i forall_e))]
  , theorem sym
     (forall '
      (lam x12 \
        forall ' (lam x13 \ impl ' (eq ' x12 ' x13) ' (eq ' x13 ' x12))))
    [then forall_i
     (bind bool x12 \
       then forall_i
        (bind bool x13 \
          then i (then sym h)))]
  , theorem not_e (forall ' (lam x2 \ impl ' (not ' x2) ' (impl ' x2 ' ff)))
     [then forall_i (bind bool x3 \ then (conv (land_tac dd)) (then i h))]
  , theorem conj
     (forall '
      (lam x12 \
       forall ' (lam x13 \ impl ' x12 ' (impl ' x13 ' (and ' x12 ' x13)))))
    [then forall_i
     (bind bool x12 \
      then forall_i (bind bool x13 \ then i (then i (then conj h))))]
  , theorem andl
     (forall ' (lam x12 \ forall ' (lam x13 \ impl ' (and ' x12 ' x13) ' x12)))
    [then forall_i
     (bind bool x12 \
      then forall_i (bind bool x13 \ then i (then (andl x13) h)))]
  , theorem andr
     (forall ' (lam x12 \ forall ' (lam x13 \ impl ' (and ' x12 ' x13) ' x13)))
    [then forall_i
     (bind bool x12 \
      then forall_i (bind bool x13 \ then i (then (andr x12) h)))]
  , theorem and_e
     (forall '
       (lam x12 \
         forall '
          (lam x13 \
            forall '
             (lam x14 \
               impl ' (and ' x12 ' x13) '
                (impl ' (impl ' x12 ' (impl ' x13 ' x14)) ' x14)))))
     [then forall_i
       (bind bool x12 \
         then forall_i
          (bind bool x13 \
            then forall_i
             (bind bool x14 \ then i (then i (thenl apply [andl, andr])))))]
  , theorem not_i (forall ' (lam x2 \ impl ' (impl ' x2 ' ff) ' (not ' x2)))
     [then forall_i (bind bool x2 \ then i (then (conv dd) h))]
  , theorem orl
     (forall ' (lam x2 \ forall ' (lam x3 \ impl ' x2 ' (or ' x2 ' x3))))
      [then forall_i
        (bind bool x12 \
          then forall_i
           (bind bool x13 \
             then i
              (then (conv dd)
                (then forall_i (bind bool x14 \ then i (then i (then apply h)))))))]
  , theorem orr
     (forall ' (lam x2 \ forall ' (lam x3 \ impl ' x3 ' (or ' x2 ' x3))))
      [then forall_i
        (bind bool x12 \
          then forall_i
           (bind bool x13 \
             then i
              (then (conv dd)
                (then forall_i (bind bool x14 \ then i (then i (then apply h)))))))]
  , theorem or_e
     (forall ' (lam x2 \ forall ' (lam x3 \ forall ' (lam x4 \ impl ' (or ' x2 ' x3) ' (impl ' (impl ' x2 ' x4) ' (impl ' (impl ' x3 ' x4) ' x4))))))
     [then forall_i
       (bind bool x12 \
         then forall_i
          (bind bool x13 \
            then forall_i
             (bind bool x14 \ then (conv (land_tac dd)) (then i forall_e))))]
  , (pi T \ theorem exists_e
    (forall ' lam f \ (impl ' (exists ' f) ' (forall ' (lam x2 \ impl ' (forall ' (lam x3 \ impl ' (f ' x3) ' x2)) ' x2))))
    [then forall_i (bind (arr T bool) x12 \ then (conv (land_tac dd)) (then i h))])
 , (pi T \ theorem exists_i
   (forall ' (lam x2 \ forall ' (lam x3 \ impl ' (x2 ' x3) ' (exists ' x2))))
   [then forall_i
     (bind (arr T bool) x12 \
       then forall_i
        (bind T x13 \
          then i
           (then (conv dd)
             (then forall_i
               (bind bool x14 \ then i (then (lforall x13) (then apply h)))))))])
 /******************* Logic *****************/
 , theorem or_commutative
   (forall ' lam a \ forall ' lam b \ eq ' (or ' a ' b) ' (or ' b ' a))
   [itaut 1]
 , theorem or_ff
   (forall ' lam a \ eq ' (or ' a ' ff) ' a)
   [itaut 1]
 , theorem or_tt
   (forall ' lam a \ eq ' (or ' a ' tt) ' tt)
   [itaut 1]
 , theorem or_idempotent
   (forall ' lam a \ eq ' (or ' a ' a) ' a)
   [itaut 1]
 , theorem or_associative
   (forall ' lam a \ forall ' lam b \ forall ' lam c \ eq ' (or ' a ' (or ' b ' c)) ' (or ' (or ' a ' b) ' c))
   [itaut 1]
 , theorem and_commutative
   (forall ' lam a \ forall ' lam b \ eq ' (and ' a ' b) ' (and ' b ' a))
   [itaut 1]
 , theorem and_tt
   (forall ' lam a \ eq ' (and ' a ' tt) ' a)
   [itaut 1]
 , theorem and_ff
   (forall ' lam a \ eq ' (and ' a ' ff) ' ff)
   [itaut 1]
 , theorem and_idempotent
   (forall ' lam a \ eq ' (and ' a ' a) ' a)
   [itaut 1]
 , theorem and_associative
   (forall ' lam a \ forall ' lam b \ forall ' lam c \ eq ' (and ' a ' (and ' b ' c)) ' (and ' (and ' a ' b) ' c))
   [itaut 1]
 , theorem and_or
   (forall ' lam a \ forall ' lam b \ forall ' lam c \ eq ' (and ' a ' (or ' b ' c)) ' (or ' (and ' a ' b) ' (and ' a ' c)))
   [itaut 1]
 , theorem or_and
   (forall ' lam a \ forall ' lam b \ forall ' lam c \ eq ' (or ' a ' (and ' b ' c)) ' (and ' (or ' a ' b) ' (or ' a ' c)))
   [itaut 1]
 , theorem ads_or_and
   (forall ' lam a \ forall ' lam b \ eq ' (or ' (and ' a ' b) ' b) ' b)
   [itaut 1]
 , theorem ads_and_or
   (forall ' lam a \ forall ' lam b \ eq ' (and ' (or ' a ' b) ' b) ' b)
   [itaut 1]
 , theorem not_or
   (forall ' lam a \ forall ' lam b \ eq ' (and ' (not ' a) ' (not ' b)) ' (not ' (or ' a ' b)))
   [itaut 2]
 , theorem not_and
   (forall ' lam a \ forall ' lam b \ impl ' (or ' (not ' a) ' (not ' b)) ' (not ' (and ' a ' b)))
   [itaut 2]
 , theorem not_not_not
   (forall ' lam p \ eq ' (not ' (not ' (not ' p))) ' (not ' p))
   [itaut 3]
 , theorem impl_not_not
   (forall ' lam a \ forall ' lam b \ impl ' (impl ' a ' b) ' (impl ' (not ' b) ' (not ' a)))
   [itaut 3]
 /******************* TESTS *****************/
 , theorem test_apply
    (impl ' p ' (impl ' (impl ' p ' (impl ' p ' q)) ' q))
    [then i (then i (then apply h))]
 , theorem test_apply2
    (impl ' p ' (impl ' (forall ' lam x \ forall ' lam y \ impl ' x ' (impl ' x ' y)) ' q))
    [then i (then i (then apply h))]
 , new_basic_type mybool myrep myabs myrepabs myabsrep
    (lam x \ exists ' lam p \ eq ' x ' (and ' p ' p))
    [then (applyth exists_i)
      (then (conv b) (then (applyth exists_i) (then (conv b) r)))]
 , theorem test_itaut_1
   (impl ' (exists ' lam g) '
     (forall ' (lam x12\ impl ' (forall ' (lam x13\ impl ' g x13 ' x12)) ' x12)))
   [itaut 4]
 ].

/* Status and dependencies of the tactics:
+dd:
+sym:
+eq_true_intro: (th tt_intro)
+forall_i: dd eq_true_intro
+conj: dd eq_true_intro
+andr: dd tt_intro
+andl: dd tt_intro
+forall_e: sym dd
+mp: andr sym dd
+i: dd andl conj
+cut: andr sym dd i
+cutth: cut
+lapply*: mp
+lforall*: mp forall_e
+apply*: lapply lforall
+applyth: cutth apply*

- f converional sometimes fails
- conv (depth_tac) diverges when applied to terms that contain
  metavariables
- repeat is not implemented using progress, that is not even there
*/

/*
-3) after main, if I do stop I see thousands of delayed goal that have
    never been resumed!

-2.5) in the proof for mybool, at the end I provide the
  witness (and X X) where X remains free (and it is not even pi-quantified).
  If bool was empty, then X could not exist. On the other hand, if X was
  empty, then there would be no need to provide the proof at all.
  In any case, the symptom for X remaining free at the end of a proof is
  one or more goals delayed on it. We never check for them and we have
  no way atm to do that. See bug -3)

-2) the test apply_2 is very slow: why?
    same for the witness for mybool

0) definitions must not be recursive (check needed)
   axioms are missing

0.5) reduce and keep documented the trusted code base

0.75) Observation: so far our HOL-Light is intuitionistic.
 Keep it like that?

1) the need to use delay is a very good news. It justifies our
implementation and it easily allow to publish. We also need to add
the corresponding constraint propagation rules that implement the
unicity of typing meta-theorem. I.e.
  |- term X A,  |- term X B ==> |- A = B

The propagation rule is however harder. Consider:

  term x A |- term (X x) B,   |- term (X 0) C
  ===> A = nat, B = C


 We will discuss about it and we basically already have
 the code in the refiner.elpi file.

1.25) major bug: I think that the proof of a theorem may now force it to
  be monomorphic, but we forget this when we assume it in check.
  Similarly: tt is defined as (x\x)=(x\x) but what is the type of those
  abstractions? It remains uninstantiated in the proof.

2) we need to fix the ELPI problems about handling of metavariables.
 I have already discussed with Enrico about them and he could have a
 shot at them. Namely:
 a) occur check + optimization to avoid it when possible
 b) unimplemented cases of restriction (IN PROGRESS)

3) once we let metavariables reach the goals, the current HOL-light 
 tactic implementation becomes too fragile. We should let the user 
 refer to hypotheses at least by number if not by name. But we better
 have a bidirectional successor/predecessor via $delay

4) we must implement type declarations and in particular inductive 
 types for HOL-light. It should also be a nice exercise in lambda-
 Prolog and the resulting code is likely to be easier than the 
 corresponding ML one. However, I never really had a look at the 
 mechanism used by HOL and we need to study it first

5) we could implement an automated theorem prover in lambdaProlog
 that works or is interfaced with the HOL-light code. There are
 complete provers like leanCOP 2.0 that are only 10 lines of code,
 but use some Prolog tricks.

6) we should do a small formalization, possibly developing a tactic,
 to prove that everything is working. For example, a decision procedure
 for rings or for linear inequations.

*/
