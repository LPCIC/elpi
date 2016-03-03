infixl ' 139.

/************ primitive rules ********/

/* seq _hypothesis_ _conclusion_ */

typ bool.
typ ind.

/*term T TY :- $print (term T TY), fail.*/
term T TY :- $is_flex T, !, $delay (term T TY) [ T ].
term T TY :- term' T TY.
term' (lam F) (arr A B) :- pi x\ term' x A => term (F x) B.
term' (F ' T) B :- term T A, term F (arr A B).
term' eq (arr A (arr A bool)).

{ /***** Trusted code base *******/

local thm, provable.

% thm : bounded tactic -> bounded sequent -> list (bounded sequent) -> o
thm C (seq Gamma G) _ :- debug, $print Gamma "|- " G " := " C, fail.

/* Remove, only for debugging */
thm daemon (seq Gamma F) [] :- term F bool.

thm r (seq Gamma (eq ' X ' X)) [] :- term X A.

thm (t Y) (seq Gamma (eq ' X ' Z))
     [ seq Gamma (eq ' X ' Y), seq Gamma (eq ' Y ' Z) ] :-
 term X A, term Y A, term Z A.
thm (m P) (seq Gamma Q) [ seq Gamma (eq ' P ' Q), seq Gamma P ].
thm b (seq Gamma (eq ' ((lam F) ' X) ' (F X))) [] :-
 term X A,
 (pi y\ term y A => term (F y) B).
thm c (seq Gamma (eq ' (F ' X) ' (G ' Y)))
 [ seq Gamma (eq ' F ' G) , seq Gamma (eq ' X ' Y) ] :-
 term X A, term Y A,
 (pi y\ term y A => term (F ' y) B),
 (pi y\ term y A => term (G ' y) B).
thm k (seq Gamma (eq ' (lam S) ' (lam T)))
 [ bind A x \  seq Gamma (eq ' (S x) ' (T x)) ] :-
 (pi y\ term y A => term (S y) B),
 (pi y\ term y A => term (T y) B).
thm s (seq Gamma (eq ' P ' Q))
 [ seq (P :: Gamma) Q, seq (Q :: Gamma) P ]
:-
 term P bool, term Q bool. /* CSC: check if required */
thm (h IGN) (seq Gamma P) [] :- append IGN [ P | Gamma2 ] Gamma.

/* TODO: unify the d and thm mechanisms? */

thm d (seq Gamma (eq ' C ' A)) [] :-
 def0 C A./*,
 pi T\ ttype T => (ttype (B T), term A (B T)). */

thm (th NAME) (seq _ G) [] :- provable NAME G.

thm (thenll TAC1 TACN) SEQ SEQS :-
 thm TAC1 SEQ NEW,
 deftacl TACN NEW TACL,
 fold2_append TACL NEW thm SEQS.

thm TAC SEQ SEQS :-
 deftac TAC SEQ XTAC,
 thm XTAC SEQ SEQS.

thm id SEQ [ SEQ ].

thm (w G) (seq Gamma F) [ seq WGamma F ] :-
 append Gamma1 [ G | Gamma2 ] Gamma,
 append Gamma1 Gamma2 WGamma.

/* remove it */
thm x (seq Gamma F) [(seq ((impl ' p ' q) :: p :: Gamma) F)].
/*thm x (seq Gamma F) [(seq ((and ' p ' q) :: Gamma) F)].*/
/*thm x (seq Gamma F) [(seq (p :: Gamma) F)].*/
/*thm x (seq Gamma F) [(seq (ff :: Gamma) F)].*/
/*thm x (seq Gamma F) [(seq (p :: q :: Gamma) F)].*/

thm (bind A TAC) (bind A SEQ) NEWL :-
 pi x \ term x A => thm (TAC x) (SEQ x) (NEW x), put_binds (NEW x) x A NEWL.

thm ww (bind A x \ SEQ) [ SEQ ].

/* debuggin only, remove it */
%thm A B C :- $print "FAILED " (thm A B C), fail.

read_in_context (bind A K) (bind A TAC) :-
 pi x \ term x A => read_in_context (K x) (TAC x).
read_in_context (seq A B) TAC :- read TAC, (TAC = backtrack, !, fail ; true).

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

mk_script (bind A T) NEW NEW_TACS (bind A T2) :- !,
 pi x \
  put_binds (NEW2 x) x A NEW,
  mk_script (T x) (NEW2 x) (NEWT x) (T2 x),
  put_binds (NEWT x) x A NEW_TACS.
mk_script ITAC NEW NEW_TACS (thenl ITAC NEW_TACS) :-
 mk_list_of_bounded_fresh NEW NEW_TACS.

prove G TACS :-
 loop true [ seq [] G ] TACS,
 $print "proof completed".

saved G TACS :-
 loop false [ seq [] G ] TACS.

check [] :- toplevel.
check [ theorem NAME GOAL TACTICS | NEXT ] :-
  not (provable NAME _),
  saved GOAL TACTICS,
  $print NAME ":" GOAL,
  !,
  provable NAME GOAL => check NEXT.
check [ new_basic_type TYPE REP ABS REPABS ABSREP P TACTICS | NEXT ] :-
  not (typ TYPE),
  not (term REP _),
  not (term ABS _),
  not (term ABSREP _),
  not (term REPABS _),
  term P (arr X bool),
  saved (exists ' P ) TACTICS,
  $print new typ TYPE,
  $print new term REP ":" (arr TYPE X),
  $print new term ABS ":" (arr X TYPE),
  $print new theorems ABSREP REPABS,
  !,
  typ TYPE =>
  term' REP (arr TYPE X) =>
  term' ABS (arr X TYPE) =>
  provable ABSREP
   (forall ' lam x \ eq ' (abs ' (rep ' x)) ' x) =>
  provable REPABS
   (forall ' lam x \ eq ' (P ' x) ' (eq ' (rep ' (abs ' x)) x)) =>
  check NEXT.
}

/************ interactive and non interactive loops ********/

print_sequent (seq Gamma G) :- $print Gamma "|-" G.
print_sequent (bind A F) :- pi x \ print_sequent (F x).

toplevel :-
 $print "Welcome to HOL extra-light",
 $print "Enter a new theorem name or stop",
 read NAME,
 ( NAME = stop, !
 ; $print "Enter its statement",
   read G,
   prove G [ TAC ],
   canonical TAC CANONICALTAC,
   $print (theorem NAME G [ CANONICALTAC ]),
   provable NAME G => toplevel).

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

deftac (orelse TAC1 TAC2) SEQ XTAC :- XTAC = TAC1 ; XTAC = TAC2.

deftac (repeat TAC) SEQ XTAC :-
 ( XTAC = then TAC (repeat TAC)
 ; XTAC = id).

deftac (printtac TAC) SEQ TAC :-
 $print "SEQ" SEQ ":=" TAC.

/********** tactics ********/

deftac h SEQ (h L).

/*** eq ***/

deftac sym (seq Gamma (eq ' L ' R)) TAC :-
 TAC = thenl (m (eq ' R ' R)) [ thenl c [ thenl c [ r , id ] , r ] , r ].

deftac eq_true_intro (seq Gamma (eq ' P ' tt)) TAC :-
 TAC = thenl s [ th tt_intro, w tt ].

/*** true ***/

/*** and ***/

deftac conj (seq Gamma (and ' P ' Q)) TAC :-
 TAC =
  then
   (thenl (m (eq ' (lam f \ f ' P ' Q) ' (lam f \ f ' tt ' tt)))
    [ then sym d
    , then k (bind _ x \ thenl c [ thenl c [ r, eq_true_intro ] , eq_true_intro ])
    ])
   ww.

/* Gamma  "|-"  q    --->   Gamma "|-" and ' p ' q*/
deftac (andr P) (seq Gamma Q) TAC :-
 TAC = (thenl (m ((lam x \ (x ' P ' Q)) ' (lam x \ (lam y \ y)))) [ thenl (m (eq ' ( (lam x \ (lam y \ y)) ' P ' Q) ' Q)) [
       thenl c [ thenl c [ r , then sym b ],  
          r ], thenl (m (eq ' (((lam x \ (lam y \ y)) ' P) ' Q) ' ((lam y \ y) ' Q))) [ thenl c [ thenl c [r , r ], b ], thenl c [b , r ] ] ],
     thenl (m ((lam f \ (f ' tt ' tt)) ' (lam x \ lam y \ y) ))     [ thenl c [ then sym (thenl (m (and ' P ' Q)) [ d , id ]), r ], thenl (m ( (lam x \ (lam y \ y)) ' tt ' tt )) [ then sym b, thenl (m ((lam y \ y) ' tt)) [ then sym (thenl c [b , r ]), thenl (m tt) [ then sym b , thenl (m (eq ' (lam x \ x) ' (lam x \ x))) [then sym d , r ] ] ] ] ] ] ).

/* (and ' p ' q) :: nil  "|-"  q */
deftac andr (seq Gamma Q) TAC :-
 mem Gamma (and ' P ' Q),
 TAC = then (andr P) h.

/* (and ' p ' q) :: nil  "|-"  p */
deftac andl (seq Gamma P) TAC :-
 mem Gamma (and ' P ' Q),
 TAC = (thenl (m ((lam x \ (x ' P ' Q)) ' (lam x \ (lam y \ x))))  [ thenl (m (eq ' ( (lam x \ (lam y \ x)) ' P ' Q) ' P)) 
      [ thenl c [ thenl c [ r , then sym b ], r ], thenl 
        (m (eq ' (((lam x \ (lam y \ x)) ' P) ' Q) ' ((lam y \ P) ' Q)))  [ thenl c  [ then c r, b ], thenl c [ b , r ] ] ],
     thenl (m ((lam f \ (f ' tt ' tt)) ' (lam x \ lam y \ x) ))    [ thenl c [ then sym (thenl (m (and ' P ' Q)) [ d , h ]), r ], thenl (m ( (lam x \ (lam y \ x)) ' tt ' tt )) [ then sym b , thenl (m ((lam y \ tt) ' tt)) [ then sym (thenl c [ b , r ]), thenl (m tt)   [ then sym b, thenl (m (eq ' (lam x \ x) ' (lam x \ x)))  [then sym d, r ] ] ] ] ] ] ).

/*** forall ***/

/* |- forall ' F  -->   |- F ' x */
deftac forall_i (seq Gamma (forall ' lam G)) TAC :-
 TAC = thenl (m (eq ' (lam G) ' (lam x \ tt)))
  [ then sym d , then k (bind _ x \ eq_true_intro) ].

/* forall ' F |- F ' T */
deftac forall_e (seq Gamma GX) TAC :-
 mem Gamma (forall ' (lam G)), GX = G X,
 TAC = thenl (m ((lam G) ' X)) [ b, thenl (m ((lam z \ tt) ' X))
  [ thenl c [then sym (thenl (m (forall ' lam G)) [d,h ]), r ],
  thenl (m tt) [then sym b, thenl (m (eq ' (lam x \ x) ' (lam x \ x))) [ then sym d, r ] ] ] ].

/* forall ' F |- f  -->  F ' a, forall ' F |- f */
deftac (lforall F A) (seq Gamma G) TAC :-
 TAC = thenl (m (impl ' (F A) ' G))
  [ thenl s [ then mp forall_e, then i h ] , i ].

/* forall ' F |- f  -->  F ' a, forall ' F |- f */
deftac (lforall A) (seq Gamma G) (lforall F A) :-
 mem Gamma (forall ' lam F).

/* forall ' F |- f  -->  F ' a, forall ' F |- f */
deftac (lforall_last A) (seq ((forall ' lam F)::Gamma) G) (lforall F A).

/*** false ***/
              
/*** impl ***/

/* |- p=>q  -->  p |- q */
deftac i (seq Gamma (impl ' P ' Q)) TAC :-
 TAC = thenl (m (eq ' (and ' P ' Q) ' P))
  [ then sym d , thenl s [ andl, thenl conj [ h, id ]]].

/* p=>q |- q  -->  |- p */
deftac (mp P) (seq Gamma Q) TAC :-
 TAC = then (andr P) (thenl (m P) [ then sym (thenl (m (impl ' P ' Q)) [ d , h ]) , id ]).

/* p=>q |- q  -->  |- p */
deftac mp (seq Gamma Q) (mp P) :-
 mem Gamma (impl ' P ' Q).

/* impl p q, Gamma |- f   --->   /*impl q f*/ Gamma |- p  ,  q, Gamma |- f */
deftac (lapply P Q) (seq Gamma F) TAC :-
 TAC =
  thenl (m (impl ' Q ' F)) [ thenl s [ then (mp Q) (then (w (impl ' Q ' F)) (then (mp P) (w (impl ' P ' Q)))) , then i (h [A]) ] , then (w (impl ' P ' Q)) (then i id) ].

/* impl p q, Gamma |- f   --->   /*impl q f*/ Gamma |- p  ,  q, Gamma |- f */
deftac lapply (seq Gamma F) (lapply P Q) :-
 mem Gamma (impl ' P ' Q).

/* impl p q, Gamma |- f   --->   /*impl q f*/ Gamma |- p  ,  q, Gamma |- f */
deftac lapply_last (seq ((impl ' P ' Q)::Gamma) F) (lapply P Q).

/*** not ***/

/*** exists ***/

/**** apply, i.e. forall + impl ****/

deftac (apply (impl ' P ' Q)) SEQ TAC :-
 TAC = thenl (lapply P Q) [ id, orelse h apply_last ].

deftac (apply (forall ' lam G)) SEQ TAC :-
 TAC = thenl (lforall G X) [ id, orelse h apply_last ].

deftac apply_last (seq (H::Gamma) F) (apply H).

deftac apply (seq Gamma F) (apply H) :-
 mem Gamma H.

/********** conversion(als) ***********/

deftac (rand_tac C) SEQ TAC :-
  TAC = thenl c [ r , C ].

deftac (rator_tac C) SEQ TAC :-
  TAC = thenl c [ C , r ].

deftac (abs_tac C) SEQ TAC :-
  TAC = then k (bind A x \ C).

deftac (land_tac C) SEQ TAC :-
  TAC = thenl c [ then c [ r, C ] , r ].

deftac (sub_tac C) SEQ TAC :-
  TAC = orelse (rand_conv C) (orelse (rator_conv C) (abs_conv C)).

deftac (try TAC) SEQ (orelse TAC id).

deftac (depth_tac C) SEQ TAC :-
  TAC = then (try C) (sub_conv (depth_conv C)).

defconv r_conv T T r.
defconv b_conv ((lam F) ' T) (F T) b.
defconv (rand_conv C) (F ' A) (F ' B) (rand_tac T) :- defconv C A B T.

deftac (conv C) (seq Gamma F) TAC :-
 defconv C F G CONVTAC,
 TAC = thenl (m G) [ then sym CONVTAC , id ].

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

def0 tt (eq ' (lam x\ x) ' (lam x\ x)).
term' tt bool.

def0 (forall ' F) (eq ' F ' (lam f \ tt)).
term' forall (arr (arr A bool) bool).

def0 (exists ' F) (forall ' (lam c \ (impl ' (forall ' (lam a \ (impl ' (F ' a) ' c))) ' c))).
term' exists (arr (arr A bool) bool).

def0 (impl ' A ' B) (eq ' (and ' A ' B) ' A).
term' impl (arr bool (arr bool bool)).

def0 ff (forall ' lam x \ x).
term' ff bool.

def0 (and ' X ' Y) (eq ' (lam f \ f ' X ' Y) ' (lam f \ f ' tt ' tt)).
term' and (arr bool (arr bool bool)).

def0 (not ' X) (impl ' X ' ff).
term' not (arr bool bool).

def0 (or ' X ' Y) (forall ' lam c \ impl ' (impl ' X ' c) ' (impl ' (impl ' Y ' c) ' c)).
term' or (arr bool (arr bool bool)).

term' p bool.
term' q bool.
term' f (arr bool bool).
term' (g X) bool :- term X bool.
term' c bool.

main :-
 check
  [ theorem th0
     (eq ' (eq ' (lam x\ x) ' (lam x\ x)) ' tt)
     (m (eq ' tt ' tt) :: c :: c :: r :: d :: r :: r :: nil)
  , theorem th0_alternative_proof0
     (eq ' (eq ' (lam x\ x) ' (lam x\ x)) ' tt)
     (thenl (m (eq ' tt ' tt)) (c :: r :: nil) ::
       thenl c (r :: d :: nil) :: r :: nil)
  , theorem th0_alternative_proof1
     (eq ' (eq ' (lam x\ x) ' (lam x\ x)) ' tt)
     [then (m (eq ' tt ' tt)) (repeat (orelse r (orelse d c)))]
  , theorem tt_intro
     tt
     (m (eq ' (lam x0\x0) ' (lam x0\x0)) :: th th0 :: r :: nil)
  , theorem test_mp_expanded q
     (x ::
       m (and ' p ' q) ::
        s ::
         andr ::
          conj ::
           h :: h :: m p :: sym :: m (impl ' p ' q) :: d :: h :: h :: nil)
  , theorem ff_elim (forall ' (lam x2 \ impl ' ff ' x2))
     [then forall_i
        (bind bool x2 \
          thenl (m (impl ' (forall ' (lam x3 \ x3)) ' x2))
           [thenl c [then sym (thenl c [r, d]), r], then i forall_e])]
  , theorem not_e (forall ' (lam x2 \ impl ' (not ' x2) ' (impl ' x2 ' ff)))
    [then forall_i
      (bind bool x2 \
        thenl (m (impl ' (impl ' x2 ' ff) ' (impl ' x2 ' ff)))
         [thenl c [thenl c [r, then sym d], r], then i h])]
  , theorem not_i (forall ' (lam x2 \ impl ' (impl ' x2 ' ff) ' (not ' x2)))
    [then forall_i (bind bool x2 \ then i (thenl (m (impl ' x2 ' ff))
      [then sym d, h]))]
  , theorem orl
     (forall ' (lam x2 \ forall ' (lam x3 \ impl ' x2 ' (or ' x2 ' x3))))
      (forall_i ::
       (bind bool x2 \ forall_i) ::
        (bind bool x2 \ bind bool x3 \ i) ::
         (bind bool
          x2 \ bind bool
            x3 \ m
                  (forall '
                    (lam
                      x4 \ impl ' (impl ' x2 ' x4) '
                            (impl ' (impl ' x3 ' x4) ' x4)))) ::
      (bind bool x2 \ bind bool x3 \ sym) ::
       (bind bool x2 \ bind bool x3 \ d) ::
        (bind bool x2 \ bind bool x3 \ forall_i) ::
         (bind bool x2 \ bind bool x3 \ bind bool x4 \ i) ::
          (bind bool x2 \ bind bool x3 \ bind bool x4 \ i) ::
           (bind bool x2 \ bind bool x3 \ bind bool x4 \ then mp h) ::
             nil)
  , theorem orr
     (forall ' (lam x2 \ forall ' (lam x3 \ impl ' x2 ' (or ' x2 ' x3))))
     [then forall_i
       (bind bool x2 \
         then forall_i
          (bind bool x3 \
            then i
             (thenl
               (m
                 (forall '
                   (lam x4 \
                     impl ' (impl ' x2 ' x4) ' (impl ' (impl ' x3 ' x4) ' x4))))
               [then sym d,
               then forall_i (bind bool x4 \ then i (then i (then (mp x2) h)))])))]
  , theorem or_e
     (forall '
       (lam x2 \
         forall '
          (lam x3 \
            forall '
             (lam x4 \
               impl ' (or ' x2 ' x3) '
                (impl ' (impl ' x2 ' x4) ' (impl ' (impl ' x3 ' x4) ' x4))))))
     [then forall_i
      (bind bool x2 \
        then forall_i
         (bind bool x3 \
           then forall_i
            (bind bool x4 \
              thenl
               (m
                 (impl '
                   (forall '
                     (lam x5 \
                       impl ' (impl ' x2 ' x5) '
                        (impl ' (impl ' x3 ' x5) ' x5))) '
                   (impl ' (impl ' x2 ' x4) ' (impl ' (impl ' x3 ' x4) ' x4))))
               [thenl c [thenl c [r, then sym d], r], then i forall_e])))]
  , theorem test_apply
    (impl ' p ' (impl ' (impl ' p ' (impl ' p ' q)) ' q))
    [then i (then i (then apply h))]
  /*, theorem test_apply2
    (impl ' p ' (impl ' (forall ' lam x \ forall ' lam y \ impl ' x ' (impl ' x ' y)) ' q))
    [then i (then i (then apply h))]*/
  , theorem exists_e
    (forall ' lam f \ (impl ' (exists ' f) ' (forall ' (lam x2 \ impl ' (forall ' (lam x3 \ impl ' (f ' x3) ' x2)) ' x2))))
    [then forall_i (bind AAAAAA f \ then i (thenl (m (exists ' f)) [d , h ]))]
 , theorem exists_i
   (forall ' (lam x2 \ forall ' (lam x3 \ impl ' (x2 ' x3) ' (exists ' x2))))
   [then forall_i (bind (arr BBBBBB bool) x2 \
    then forall_i (bind BBBBBB x3 \
    then i
    (thenl (m (forall ' (lam x4 \ impl ' (forall ' (lam x5 \ impl ' (x2 ' x5) ' x4)) ' x4)))
    [then sym d,
     then forall_i (bind bool x4 \
     then i (then (lforall x3) (then mp h)))])))]
 , new_basic_type mybool myrep myabs myrepabs myabsrep
    (lam x \ exists ' lam p \ eq ' x ' (and ' p ' p))
    [ daemon ]
 ].

/*
BUGS:
- forall ' lam x \ tt
  forall_i fails
- major bug: theorems are forced to be monomorphic. E.g.
  exists_i only inhabits (exists ' lam x \ F ' x) where F
  has type (X -> bool) for a fixed existentially quantified
  but uninstantiated variable X.

  This is yet another case of lack of Hindley-Milner
  polymorphism.
*/

/*
1. the need to use delay is a very good news. It justifies our
implementation and it easily allow to publish. We also need to add
the corresponding constraint propagation rules that implement the
unicity of typing meta-theorem. I.e.
  |- term X A,  |- term X B ==> |- A = B

The propagation rule is however harder. Consider:

  term x A |- term (X x) B,   |- term (X 0) C
  ===> A = nat, B = C


 We will discuss about it and we basically already have
 the code in the refiner.elpi file.

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
