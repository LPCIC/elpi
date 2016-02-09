infixl ' 139.

/************ primitive rules ********/

/* seq _hypothesis_ _conclusion_ */

/*term T TY :- $print (term T TY), fail.*/
term (lam F) (arr A B) :- pi x\ term x A => term (F x) B.
term (F ' T) B :- term T A, term F (arr A B).
term eq (arr A (arr A bool)).

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
thm h (seq Gamma P) [] :- mem Gamma P.

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
loop INTERACTIVE [ SEQ | OLD ] [ TAC | TACS ] :-
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
   TAC = ITAC,
   %$print "OK" (loop INTERACTIVE SEQS TACS),
   loop INTERACTIVE SEQS TACS
 ; (INTERACTIVE = true, !, $print "error" ;
    $print "aborted", halt),
   loop INTERACTIVE [ SEQ | OLD ] [ TAC | TACS ] ).
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
   prove G TACS,
   $print (theorem NAME G TACS),
   provable NAME G => toplevel).

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

mem [ X | _ ] X, !.
mem [ _ | XS ] X :- mem XS X.

/*mk_constant_list A B C :- debug, $print (mk_constant_list A B C), fail.*/
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
deftac (cutandr P) (seq Gamma Q) TAC :-
 TAC = (thenl (m ((lam x \ (x ' P ' Q)) ' (lam x \ (lam y \ y)))) [ thenl (m (eq ' ( (lam x \ (lam y \ y)) ' P ' Q) ' Q)) [
       thenl c [ thenl c [ r , then sym b ],  
          r ], thenl (m (eq ' (((lam x \ (lam y \ y)) ' P) ' Q) ' ((lam y \ y) ' Q))) [ thenl c [ thenl c [r , r ], b ], thenl c [b , r ] ] ],
     thenl (m ((lam f \ (f ' tt ' tt)) ' (lam x \ lam y \ y) ))     [ thenl c [ then sym (thenl (m (and ' P ' Q)) [ d , id ]), r ], thenl (m ( (lam x \ (lam y \ y)) ' tt ' tt )) [ then sym b, thenl (m ((lam y \ y) ' tt)) [ then sym (thenl c [b , r ]), thenl (m tt) [ then sym b , thenl (m (eq ' (lam x \ x) ' (lam x \ x))) [then sym d , r ] ] ] ] ] ] ).

/* (and ' p ' q) :: nil  "|-"  q */
deftac andr (seq Gamma Q) TAC :-
 mem Gamma (and ' P ' Q),
 TAC = then (cutandr P) h.

/* (and ' p ' q) :: nil  "|-"  p */
deftac andl (seq Gamma P) TAC :-
 mem Gamma (and ' P ' Q),
 TAC = (thenl (m ((lam x \ (x ' P ' Q)) ' (lam x \ (lam y \ x))))  [ thenl (m (eq ' ( (lam x \ (lam y \ x)) ' P ' Q) ' P)) 
      [ thenl c [ thenl c [ r , then sym b ], r ], thenl 
        (m (eq ' (((lam x \ (lam y \ x)) ' P) ' Q) ' ((lam y \ P) ' Q)))  [ thenl c  [ then c r, b ], thenl c [ b , r ] ] ],
     thenl (m ((lam f \ (f ' tt ' tt)) ' (lam x \ lam y \ x) ))    [ thenl c [ then sym (thenl (m (and ' P ' Q)) [ d , h ]), r ], thenl (m ( (lam x \ (lam y \ x)) ' tt ' tt )) [ then sym b , thenl (m ((lam y \ tt) ' tt)) [ then sym (thenl c [ b , r ]), thenl (m tt)   [ then sym b, thenl (m (eq ' (lam x \ x) ' (lam x \ x)))  [then sym d, r ] ] ] ] ] ] ).

/*** forall ***/

deftac forall_e (seq Gamma GX) TAC :-
 mem Gamma (forall ' (lam G)), GX = G X,
 TAC = thenl (m ((lam G) ' X)) [ b, thenl (m ((lam z \ tt) ' X))
  [ thenl c [then sym (thenl (m (forall ' lam G)) [d,h ]), r ],
  thenl (m tt) [then sym b, thenl (m (eq ' (lam x \ x) ' (lam x \ x))) [ then sym d, r ] ] ] ].

deftac forall_i (seq Gamma (forall ' lam G)) TAC :-
 TAC = thenl (m (eq ' (lam G) ' (lam x \ tt)))
  [ then sym d , then k (bind _ x \ eq_true_intro) ].

/*** false ***/
              
/*** impl ***/

deftac (mp P) (seq Gamma Q) TAC :-
 TAC = then (cutandr P) (thenl (m P) [ then sym (thenl (m (impl ' P ' Q)) [ d , h ]) , id ]).

deftac mp (seq Gamma Q) (mp P) :-
 mem Gamma (impl ' P ' Q).

deftac i (seq Gamma (impl ' P ' Q)) TAC :-
 TAC = thenl (m (eq ' (and ' P ' Q) ' P))
  [ then sym d , thenl s [ andl, thenl conj [ h, id ]]].

/*** not ***/

/*** lapply ***/

/* impl p q |- f   --->   impl q f |- p  ,  q |- f */
deftac (lapply P Q) (seq Gamma F) TAC :-
 TAC =
  thenl (m (impl ' Q ' F)) [ thenl s [ then (mp Q) (mp P) , then i h ] , then i id ].

/* impl p q |- f   --->   impl q f |- p  ,  q |- f */
deftac lapply (seq Gamma F) (lapply P Q) :-
 mem Gamma (impl ' P ' Q).

/* impl p q |- f   --->   impl q f |- p  ,  q |- f */
deftac lapply_last (seq ((impl ' P ' Q)::Gamma) F) (lapply P Q).

deftac (apply P Q) SEQ TAC :-
 TAC = thenl (lapply P Q) [ id, orelse h apply_last ].

deftac apply_last (seq ((impl ' P ' Q)::Gamma) F) (apply P Q).

deftac apply (seq Gamma F) (apply P Q) :-
 mem Gamma (impl ' P ' Q).

/********** the library ********/

def0 tt (eq ' (lam x\ x) ' (lam x\ x)).
term tt bool.

def0 (forall ' F) (eq ' F ' (lam f \ tt)).
term forall (arr (arr A bool) bool).

def0 (impl ' A ' B) (eq ' (and ' A ' B) ' A).
term impl (arr bool (arr bool bool)).

def0 ff (forall ' lam x \ x).
term ff bool.

def0 (and ' X ' Y) (eq ' (lam f \ f ' X ' Y) ' (lam f \ f ' tt ' tt)).
term and (arr bool (arr bool bool)).

def0 (not ' X) (impl ' X ' ff).
term not (arr bool bool).

def0 (or ' X ' Y) (forall ' lam c \ impl ' (impl ' X ' c) ' (impl ' (impl ' Y ' c) ' c)).
term or (arr bool (arr bool bool)).

term p bool.
term q bool.
term f (arr bool bool).
term (g X) bool :- term X bool.

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
  , theorem ff_elim
     (forall ' lam p \ impl ' ff ' p)
     (forall_i ::
       (bind _ p \ m (impl ' (forall ' (lam x2 \ x2)) ' p)) ::
       (bind _ p \ c) ::
       sym :: c :: r :: d ::
       (bind _ p \ r) ::
       (bind _ p \ i) ::
       (bind _ p \ forall_e) :: nil)
  , theorem ff_elim_alt
     (forall ' lam p \ impl ' ff ' p)
     [then forall_i
       (bind A p \
         thenl (m (impl ' (forall ' (lam x2 \ x2)) ' p))
         [ thenl c [ then sym (thenl c [ r , d ]) , r ],
           then i forall_e ] )]
  , theorem not_e (forall ' (lam x2 \ impl ' (not ' x2) ' (impl ' x2 ' ff)))
     (forall_i ::
       (bind bool x2 \ m (impl ' (impl ' x2 ' ff) ' (impl ' x2 ' ff))) ::
        (bind bool x2 \ c) ::
         (bind bool x2 \ c) ::
          r ::
           (bind bool x2 \ sym) ::
            (bind bool x2 \ d) ::
             (bind bool x2 \ r) :: (bind bool x2 \ i) :: (bind bool x2 \ h) :: nil)
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
 ].
