infixl ' 139.

/* seq _hypothesis_ _conclusion_ */

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
 term P bool, term Q bool, /* CSC: check if required */
thm (seq Gamma P) h [] :- mem Gamma P.

thm (seq Gamma (eq ' C ' A)) d [] :-
 def1 C A./*,
 pi T\ ttype T => (ttype (B T), term A (B T)). */

def1 tt (eq ' (lam x\ x) ' (lam x\ x)).
term tt bool.

print_seq (seq Gamma G) :- $print Gamma "|-" G.

print_all_seqs []. 
print_all_seqs [ SEQ | SEQS ] :-
 print_all_seqs SEQS,
 print_seq SEQ.
print_all_seqs (bind A F) :-
 pi x \ ($print x ":" A, print_all_seqs (F x)).

loop true [] [] :- $print "proof completed".
loop false [] [].
loop INTERACTIVE [ SEQ | OLD ] [ TAC | TACS ] :-
 (INTERACTIVE = true, !,
   print_all_seqs [ SEQ | OLD ],
   read ITAC
 ; ITAC = TAC),
 ( thm SEQ ITAC NEW,
   append NEW OLD SEQS,
   TAC = ITAC,
   loop INTERACTIVE SEQS TACS
 ; ITAC = backtrack, !,
   fail
 ; (INTERACTIVE = true, !, $print "error" ;
    $print "aborted", halt),
   loop INTERACTIVE [ SEQ | OLD ] [ TAC | TACS ] ).
loop (bind A F) TACS :-
 pi x \ term x A => loop (F x) TACS.

prove G :-
 loop true [ seq [] G ] TACS,
 $print TACS.

saved G TACS :-
 loop false [ seq [] G ] TACS.

check :-
 saved (eq ' (eq ' (lam x\ x) ' (lam x\ x)) ' tt)
  (m (eq ' tt ' tt) :: c :: c :: r :: d :: r :: r :: nil).

/*tactic (bINARY_CONGR X Y) (c X (c Y r)).
thm G X :- tactic X Y, thm G Y.*/

/* blist ::= [] | X :: blist | bind A F
   where  F is x\ blist and A is the type of x */

append [] L L.
append [ X | XS ] L [ X | RES ] :- append XS L RES.
append (bind A F) L (bind A FL) :-
 pi x \ append (F x) L (FL x).

mem [ X | _ ] X, !.
mem [ _ | XS ] X :- mem XS X.
