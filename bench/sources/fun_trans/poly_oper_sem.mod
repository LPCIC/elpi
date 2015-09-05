module poly_oper_sem.

accumulate oper_sem.
accumulate poly_terms.

eval (tlam _TP F) (lam F).

eval (trec _TP F) (lam (F (rec F))).

eval (tlet _S T1 F) V :-
  eval T1 V1,
  eval (F V1) V.

eval (tabs F) V :- pi tp\ eval (F tp) V.
