infixl ' 139.

/************ primitive rules ********/

/* seq _hypothesis_ _conclusion_ */

/*term T TY :- $print (term T TY), fail.*/
term (lam F) (impl A B) :- pi x\ term x A => term (F x) B.
term (F ' T) B :- term T A, term F (impl A B).
term eq (impl A (impl A bool)).

/*thm (seq Gamma G) C _ :- $print Gamma "|- " G " := " C, fail.*/
thm (seq Gamma (eq ' X ' X)) r [] :- term X A.
thm (seq Gamma (eq ' X ' Z)) (t Y)
     [ seq Gamma (eq ' X ' Y), seq Gamma (eq ' Y ' Z) ] :-
 term X A, term Y A, term Z A.
thm (seq Gamma Q) (m P) [ seq Gamma (eq ' P ' Q), seq Gamma P ].
thm (seq Gamma (eq ' ((lam F) ' X) ' (F X))) b [] :-
 term X A,
 (pi y\ term y A => term (F y) B).
thm (seq Gamma (eq ' (F ' X) ' (G ' Y))) c
 [ seq Gamma (eq ' F ' G) , seq Gamma (eq ' X ' Y) ] :-
 term X A, term Y A,
 (pi y\ term y A => term (F ' y) B),
 (pi y\ term y A => term (G ' y) B).
thm (seq Gamma (eq ' (lam S) ' (lam T))) k
 (bind A x \ [ seq Gamma (eq ' (S x) ' (T x)) ]) :-
 (pi y\ term y A => term (S y) B),
 (pi y\ term y A => term (T y) B).
thm (seq Gamma (eq ' P ' Q)) s
 [ seq ((hyp P) :: Gamma) Q, seq ((hyp Q) :: Gamma) P ]
:-
 term P bool, term Q bool. /* CSC: check if required */
thm (seq Gamma P) h [] :- mem Gamma P.

thm (seq Gamma (eq ' C ' A)) d [] :-
 def0 C A./*,
 pi T\ ttype T => (ttype (B T), term A (B T)). */

thm (seq _ G) (th NAME) [] :- provable NAME G.

/************ interactive and non interactive loops ********/

print_seq (seq Gamma G) :- $print Gamma "|-" G.

print_all_seqs []. 
print_all_seqs [ SEQ | SEQS ] :-
 print_all_seqs SEQS,
 print_seq SEQ.
print_all_seqs (bind A F) :-
 pi x \ ($print x ":" A, print_all_seqs (F x)).

/*loop INTERACTIVE SEQS TACS :- $print (loop INTERACTIVE SEQS TACS), fail.*/
loop _ [] [].
loop INTERACTIVE [ SEQ | OLD ] [ TAC | TACS ] :-
 (INTERACTIVE = true, !,
   print_all_seqs [ SEQ | OLD ],
   read ITAC
 ; ITAC = TAC),
 ( tactic SEQ ITAC NEW,
   append NEW OLD SEQS,
   TAC = ITAC,
   loop INTERACTIVE SEQS TACS
 ; ITAC = backtrack, !,
   fail
 ; (INTERACTIVE = true, !, $print "error" ;
    $print "aborted", halt),
   loop INTERACTIVE [ SEQ | OLD ] [ TAC | TACS ] ).
loop INTERACTIVE (bind A F) TACS :-
 pi x \ term x A => loop INTERACTIVE (F x) TACS.

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

toplevel :-
 $print "Welcome to HOL extra-light",
 $print "Enter a new theorem name",
 read NAME,
 $print "Enter its statement",
 read G,
 prove G TACS,
 $print (theorem NAME G TACS),
 provable NAME G => toplevel.

/************ library of basic data types ********/
/* blist ::= [] | X :: blist | bind A F
   where  F is x\ blist and A is the type of x */

append [] L L.
append [ X | XS ] L [ X | RES ] :- append XS L RES.
append (bind A F) L (bind A FL) :-
 pi x \ append (F x) L (FL x).

fold_append [] _ [].
fold_append [ X | XS ] F OUTS :-
 F X OUT, fold_append XS F OUTS2, append OUT OUTS2 OUTS.
fold_append (bind A G) F (bind A OUT) :-
 pi x \ term x A => fold_append (G x) F (OUT x).

fold2_append [] [] _ [].
fold2_append [ X | XS ] [ Y | YS ] F OUTS :-
 F X Y OUT, fold2_append XS YS F OUTS2, append OUT OUTS2 OUTS.
fold2_append (bind A G) YS F (bind A OUT) :-
 pi x \ fold2_append (G x) YS F (OUT x).

mem [ X | _ ] X, !.
mem [ _ | XS ] X :- mem XS X.

/********** tactics and tacticals ********/

/*tactic (seq Gamma G) C _ :- $print Gamma "|- " G " := " C, fail.*/

tactic SEQ T SEQS :-
 thm SEQ T SEQS.

tactic (seq Gamma (eq ' L ' R)) sym SEQS :-
 TAC = thenl (m (eq ' R ' R)) [ thenl c [ thenl c [ r , id ] , r ] , r ],
 tactic (seq Gamma (eq ' L ' R)) TAC SEQS.

tactic (seq Gamma (eq ' P ' tt)) eq_true_intro SEQS :-
 TAC = thenl s [ th tt_intro, id ],
 tactic (seq Gamma (eq ' P ' tt)) TAC SEQS.

tactic (seq Gamma (and ' P ' Q)) conj SEQS :-
 TAC =
  thenl (m (eq ' (lam f \ f ' P ' Q) ' (lam f \ f ' tt ' tt)))
   [ then sym d
   , then k (thenl c [ thenl c [ r, eq_true_intro ] , eq_true_intro ])
   ],
 tactic (seq Gamma (and ' P ' Q)) TAC SEQS.

tactic (seq Gamma P) andl SEQS :-
 mem Gamma (and ' P ' Q),
 TAC = (thenl (m ((lam x \ (x ' P ' Q)) ' (lam x \ (lam y \ x))))  [ thenl (m (eq ' ( (lam x \ (lam y \ x)) ' P ' Q) ' P)) 
      [ thenl c [ thenl c [ then r id, then sym (then b id)           ], (then r id) ], thenl 
        (m (eq ' (((lam x \ (lam y \ x)) ' P) ' Q) ' ((lam y \ P) ' Q)))  [ thenl c  [ thenl c [then r id, then r id], 
            then b id ], thenl c [then b id, then r id] ] ],
     thenl (m ((lam f \ (f ' tt ' tt)) ' (lam x \ lam y \ x) ))    [ thenl c [ then sym (thenl (m (and ' P ' Q)) [ then d id,     then h id ]), then r id ], thenl (m ( (lam x \ (lam y \ x)) ' tt ' tt )) [ then sym (then b id), thenl (m ((lam y \ tt) ' tt)) [ then sym (thenl c [then b id, then r id]), thenl (m tt)   [ then sym (then b id), thenl (m (eq ' (lam x \ x) ' (lam x \ x)))  [then sym (then d id), then r id] ] ] ] ] ] ),
 tactic (seq Gamma P) TAC SEQS.


tactic (seq Gamma Q) andr SEQS :-
 mem Gamma (and ' P ' Q),
 TAC = (thenl (m ((lam x \ (x ' P ' Q)) ' (lam x \ (lam y \ y)))) [ thenl (m (eq ' ( (lam x \ (lam y \ y)) ' P ' Q) ' Q)) [
       thenl c [ thenl c [ then r id, then sym (then b id) ],  
          (then r id) ], thenl (m (eq ' (((lam x \ (lam y \ y)) ' P) ' Q) ' ((lam y \ y) ' Q))) [ thenl c [ thenl c [then r id, then r id], then b id ], thenl c [then b id, then r id] ] ],
     thenl (m ((lam f \ (f ' tt ' tt)) ' (lam x \ lam y \ y) ))     [ thenl c [ then sym (thenl (m (and ' P ' Q)) [ then d id,   then h id ]), then r id ], thenl (m ( (lam x \ (lam y \ y)) ' tt ' tt )) [ then sym (then b id), thenl (m ((lam y \ y) ' tt)) [ then sym (thenl c [then b id, then r id]), thenl (m tt) [     then sym (then b id), thenl (m (eq ' (lam x \ x) ' (lam x \ x))) [then sym (then d id), then r id] ] ] ] ] ] ),
 tactic (seq Gamma Q) TAC SEQS.

/********** tacticals ********/

tactic SEQ id [ SEQ ].

tactic SEQ (then TAC1 TAC2) SEQS :-
 tactic SEQ TAC1 NEW,
 fold_append NEW (seq \ out \ tactic seq TAC2 out) SEQS.

tactic SEQ (thenl TAC1 TACL) SEQS :-
 tactic SEQ TAC1 NEW,
 fold2_append NEW TACL (seq \ tac \ out \ tactic seq tac out) SEQS.

tactic SEQ (orelse TAC1 TAC2) SEQS :-
   tactic SEQ TAC1 SEQS
 ; tactic SEQ TAC2 SEQS.

tactic SEQ (repeat TAC) SEQS :-
 (tactic SEQ TAC NEW,
  fold_append NEW (seq \ out \ tactic seq (repeat TAC) out) SEQS
 ; SEQS = SEQ).

/********** the library ********/

def0 tt (eq ' (lam x\ x) ' (lam x\ x)).
term tt bool.

/*def0 (forall ' F) (eq ' F ' (lam f \ tt)).
term forall (impl (A impl bool) bool).*/

def0 (and ' X ' Y) (eq ' (lam f \ f ' X ' Y) ' (lam f \ f ' tt ' tt)).
term and (impl bool (impl bool bool)).

term p bool.
term q bool.

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
     (then (m (eq ' tt ' tt)) (repeat (orelse r (orelse d c))) :: nil)
  , theorem tt_intro
     tt
     (m (eq ' (lam x0\x0) ' (lam x0\x0)) :: th th0 :: r :: nil)
  ].
