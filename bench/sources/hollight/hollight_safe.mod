infixl ' 139.

/************ primitive rules ********/

/* seq _hypothesis_ _conclusion_ */

/*term T TY :- $print (term T TY), fail.*/
term T TY :- $is_flex T, !, $delay (term T TY) [ T ].
term T TY :- term' T TY.
term' (lam F) (arr A B) :- pi x\ term' x A => term (F x) B.
term' (F ' T) B :- term T A, term F (arr A B).
term' eq (arr A (arr A bool)).

{ /***** Trusted code base *******/

local thm, provable.

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
 (bind A x \ [ seq Gamma (eq ' (S x) ' (T x)) ]) :-
 (pi y\ term y A => term (S y) B),
 (pi y\ term y A => term (T y) B).
thm s (seq Gamma (eq ' P ' Q))
 [ seq (P :: Gamma) Q, seq (Q :: Gamma) P ]
:-
 term P bool, term Q bool. /* CSC: check if required */
thm (h IGN) (seq Gamma P) [] :- append IGN [ P | Gamma2 ] Gamma.

thm d (seq Gamma (eq ' C ' A)) [] :-
 def0 C A./*,
 pi T\ ttype T => (ttype (B T), term A (B T)). */

thm (th NAME) (seq _ G) [] :- provable NAME G.

thm (thenll TAC1 TACN) SEQ SEQS :-
 %$print "THM ??" (thm TAC1 SEQ NEW0),
 thm TAC1 SEQ NEW0,
 %$print "THM OK" (thm TAC1 SEQ NEW0),
 push_binds NEW0 NEW,
 %$print "PUSH BINDS" (push_binds NEW0 NEW),
 deftacl TACN NEW TACL,
 %$print "DEFTACL OK" (deftacl TACN NEW TACL),
 %$print "FOLD2_APPEND" (fold2_append NEW TACL (seq \ tac \ out \ thm tac seq out) SEQS),
 fold2_append NEW TACL (seq \ tac \ out \ thm tac seq out) SEQS.
 %$print "FOLD2_APPEND_OK" (fold2_append NEW TACL (seq \ tac \ out \ thm tac seq out) SEQS).

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

thm (bind A TAC) (bind A SEQ) (bind A NEW) :-
 pi x \ term x A => thm (TAC x) (SEQ x) (NEW x).

/* debuggin only, remove it */
%thm A B C :- $print "FAILED " (thm A B C), fail.

read_in_context (bind A K) (bind A TAC) :-
 pi x \ term x A => read_in_context (K x) (TAC x).
read_in_context (seq A B) TAC :- read TAC, (TAC = backtrack, !, fail ; true).

%loop INTERACTIVE SEQS TACS :- $print "LOOP" (loop INTERACTIVE SEQS TACS), fail.
loop _ [] [].
loop INTERACTIVE [ SEQ | OLD ] [ TAC | OTHER_TACS ] :-
 (INTERACTIVE = true, !,
   $print,
   print_all_seqs [ SEQ | OLD ],
   %$print "READ_IN_CONTEXT" SEQ,
   read_in_context SEQ ITAC
   %, $print "READ" ITAC
 ; ITAC = TAC),
 ( thm ITAC SEQ NEW0,
   %$print "OK" (thm ITAC SEQ NEW0),
   push_binds NEW0 NEW,
   %$print "OK" (push_binds NEW0 NEW),
   append NEW OLD SEQS,
   %$print "OK" (append NEW OLD SEQS),
   (INTERACTIVE = true, !,
      %$print "OK" (mk_fresh_list NEW NEW_TACS),
      mk_fresh_list NEW NEW_TACS,
      %$print "OK" (TAC = thenl ITAC NEW_TACS),
      TAC = thenl ITAC NEW_TACS,
      append NEW_TACS OTHER_TACS TACS
   ; TACS = OTHER_TACS ),
   %$print "OK" (loop INTERACTIVE SEQS TACS),
   loop INTERACTIVE SEQS TACS
 ; (INTERACTIVE = true, !, $print "error" ;
    $print "aborted", halt),
   loop INTERACTIVE [ SEQ | OLD ] [ TAC | OTHER_TACS ] ).
%loop INTERACTIVE SEQS TACS :- $print "FAIL" (loop INTERACTIVE SEQS TACS), fail.

prove G TACS :-
 loop true [ seq [] G ] TACS,
 $print "proof completed".

saved G TACS :-
 loop false [ seq [] G ] TACS.

check [] :- toplevel.
check [ theorem NAME GOAL TACTICS | NEXT ] :-
  saved GOAL TACTICS,
  $print NAME ":" GOAL,
  !,
  provable NAME GOAL => check NEXT.

}

/************ interactive and non interactive loops ********/

print_seq (seq Gamma G) :- $print Gamma "|-" G.
print_seq (bind A F) :- pi x \ print_seq (F x).

print_all_seqs []. 
print_all_seqs [ SEQ | SEQS ] :-
 print_all_seqs SEQS,
 print_seq SEQ.

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

/********* creating a nice script for the user ********/
pull_bind [] (bind _ x \ []).
pull_bind [bind A T | XS] (bind A x \ [ T x | YS x ]) :-
 pull_bind XS (bind A YS).

pull_binds L1 L3 :-
 pull_bind L1 L2, !,
 (L2 = bind A F, !,
  (pi x \ pull_binds (F x) (G x)),
  L3 = bind A G
 ; L3 = L2).
pull_binds L L.

pull_binds_from_thenl (thenl (bind A F) (bind A G)) (bind A T) :- !,
 pi x \ pull_binds_from_thenl (thenl (F x) (G x)) (T x).
pull_binds_from_thenl T T.

/* turns thenl o bind into bind o thenl */
canonical1 (thenl T []) T :- !.
canonical1 (thenl T L1) OTAC :- !,
 blist_map L1 canonical1 L2,
 pull_binds L2 L3,
 pull_binds_from_thenl (thenl T L3) OTAC.
canonical1 (bind A T1) (bind A T2) :- !,
 pi x \ canonical1 (T1 x) (T2 x).
canonical1 T T.

/* turns thenl into then */
canonical2 (thenl T L) OTAC :- !,
 blist_map L canonical2 L2,
 (mk_constant_list L2 S L2, !,
  (S = [], !, OTAC = T ; OTAC = then T S)
 ; OTAC = thenl T L2).
canonical2 (bind A T1) (bind A T2) :- !,
 pi x \ canonical2 (T1 x) (T2 x).
canonical2 T T.

/* turns thenl into then and thenl o bind into bind o thenl */
canonical T1 T3 :-
 canonical1 T1 T2, /* first pass: take out binds */
 canonical2 T2 T3. /* second pass: introduce then */

/************ library of basic data types ********/
/* blist ::= [] | X :: blist | bind A F
   where  F is x\ blist and A is the type of x */

%put_binds A B C D :- $print "PUT BINDS" (put_binds A B C D), fail.
put_binds A [] C [].
put_binds X [ YX | YSX ] A [ YX | YYS ] :-
 %$print "PRUNING BINDER",
 !, put_binds X YSX A YYS.
put_binds X [ YX | YSX ] A [ bind A Y | YYS ] :-
 YX = Y X, put_binds X YSX A YYS.

%push_binds A B :- $print (push_binds A B), fail.
push_binds (bind A L) RES :-
 pi x \ (push_binds (L x) (L2 x), put_binds x (L2 x) A RES).
push_binds [] [].
push_binds XXS YYS :- XXS = [ X | XS ], YYS = XXS.
%push_binds A B :- $print "FAIL" (push_binds A B), fail.

%append A B C :- $print (append_aux A B C), fail.
append [] L L.
append [ X | XS ] L [ X | RES ] :- append XS L RES.
%append A B C :- $print "FAIL" (append_aux A B C), fail.

%fold2_append A B C D :- $print "ENTERING" (fold2_append A B C D), fail.
fold2_append [] [] _ [].
fold2_append [ X | XS ] [ Y | YS ] F OUTS :-
 F X Y OUT0, fold2_append XS YS F OUTS2, push_binds OUT0 OUT, append OUT OUTS2 OUTS.
%fold2_append A B C D :- $print "FAIL" (fold2_append A B C D), fail.

blist_map [] _ [].
blist_map [X|XS] F [Y|YS] :- 
 F X Y, 
 blist_map XS F YS.
blist_map (bind A L) F (bind A M) :-
 pi x \ term X A => blist_map (L x) F (M x).

mem [ X | _ ] X, !.
mem [ _ | XS ] X :- mem XS X.

/*mk_constant_list A B C :- debug, $print (mk_constant_list A B C), fail.*/
mk_constant_list [] _ [].
mk_constant_list [_|L] X [X|R] :- mk_constant_list L X R.
mk_constant_list (bind A L1) (bind A X) (bind A L2) :- 
 pi x \ mk_constant_list (L1 x) (X x) (L2 x).

mk_fresh_list [] [].
mk_fresh_list [_|L] [X|R] :- mk_fresh_list L R.

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
  thenl (m (eq ' (lam f \ f ' P ' Q) ' (lam f \ f ' tt ' tt)))
   [ then sym d
   , then k (bind _ x \ thenl c [ thenl c [ r, eq_true_intro ] , eq_true_intro ])
   ].

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
     (thenl (bind bool x2 \ m (impl ' (forall ' (lam x3 \ x3)) ' x2))
     [thenl (bind bool x2 \ c)
       [then sym (thenl c [r, d])
       ,bind bool x2 \ r]
     ,bind bool x2 \ then i forall_e])]
  , theorem not_e (forall ' (lam x2 \ impl ' (not ' x2) ' (impl ' x2 ' ff)))
    [then forall_i
     (thenl (bind bool x2 \ m (impl ' (impl ' x2 ' ff) ' (impl ' x2 ' ff)))
      [thenl (bind bool x2 \ c)
        [thenl (bind bool x2 \ c)
          [r, bind bool x2 \ then sym d]
        , bind bool x2 \ r]
      , bind bool x2 \ then i h])]
  , theorem not_i (forall ' (lam x2 \ impl ' (impl ' x2 ' ff) ' (not ' x2)))
     (forall_i ::
       (bind bool x2 \ i) ::
        (bind bool x2 \ m (impl ' x2 ' ff)) ::
         (bind bool x2 \ sym) :: (bind bool x2 \ d) :: (bind bool x2 \ h) :: nil)
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
     (forall ' (lam x2 \ forall ' (lam x3 \ impl ' x2 ' (or ' x3 ' x2))))
      (forall_i ::
       (bind bool x2 \ forall_i) ::
        (bind bool x2 \ bind bool x3 \ i) ::
         (bind bool
          x2 \ bind bool
            x3 \ m
                  (forall '
                    (lam
                      x4 \ impl ' (impl ' x3 ' x4) '
                            (impl ' (impl ' x2 ' x4) ' x4)))) ::
      (bind bool x2 \ bind bool x3 \ sym) ::
       (bind bool x2 \ bind bool x3 \ d) ::
        (bind bool x2 \ bind bool x3 \ forall_i) ::
         (bind bool x2 \ bind bool x3 \ bind bool x4 \ i) ::
          (bind bool x2 \ bind bool x3 \ bind bool x4 \ i) ::
           (bind bool x2 \ bind bool x3 \ bind bool x4 \ mp) ::
            (bind bool x2 \ bind bool x3 \ bind bool x4 \ h) :: nil)
  , theorem or_e
     (forall '
       (lam
         x2 \ forall '
               (lam
                 x3 \ forall '
                       (lam
                         x4 \ impl ' (or ' x2 ' x3) '
                               (impl ' (impl ' x2 ' x4) '
                                 (impl ' (impl ' x3 ' x4) ' x4))))))
     (forall_i ::
       (bind bool x2 \ forall_i) ::
        (bind bool x2 \ bind bool x3 \ forall_i) ::
         (bind bool
          x2 \ bind bool
                x3 \ bind bool
                      x4 \ m
                            (impl '
                              (forall '
                                (lam
                                  x5 \ impl ' (impl ' x2 ' x5) '
                                        (impl ' (impl ' x3 ' x5) ' x5))) '
                              (impl ' (impl ' x2 ' x4) '
                                (impl ' (impl ' x3 ' x4) ' x4)))) ::
          (bind bool x2 \ bind bool x3 \ bind bool x4 \ c) ::
           (bind bool x2 \ bind bool x3 \ c) ::
            r ::
             (bind bool x2 \ bind bool x3 \ sym) ::
              (bind bool x2 \ bind bool x3 \ d) ::
               (bind bool x2 \ bind bool x3 \ bind bool x4 \ r) ::
                (bind bool x2 \ bind bool x3 \ bind bool x4 \ i) ::
                 (bind bool x2 \ bind bool x3 \ bind bool x4 \ forall_e) :: nil)
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

 ].

/*
BUGS:
- major bug: theorems are forced to be monomorphic. E.g.
  exists_i only inhabits (exists ' lam x \ F ' x) where F
  has type (X -> bool) for a fixed existentially quantified
  but uninstantiated variable X.

  This is yet another case of lack of Hindley-Milner
  polymorphism.

TODO:
- back to the blackboard for bind-pushing and erasing and
  script pretty-printing. exists_e shows the problem
*/
