module oper_sem.

accumulate terms.

eval T T :- T = u.

eval (pair T1 T2) (pair V1 V2) :-
  eval T1 V1,
  eval T2 V2.

eval (fst T) V1 :- eval T (pair V1 _V2).
eval (snd T) V2 :- eval T (pair _V1 V2).

eval (inl T) (inl V) :- eval T V.
eval (inr T) (inr V) :- eval T V.

eval (case CT LF RF) V :-
  eval CT CV,
  ( % CASE: condition is "inl L"
    CV = inl L,
    eval (LF L) V
  ; % CASE: condition is "inr R"
    CV = inr R,
    eval (RF R) V
  ).

eval T T :- T = lam _.

eval T (lam (F T)) :- T = rec F.

eval (app T1 T2) V :-
  eval T1 (lam F),
  eval T2 V2,
  eval (F V2) V.

eval (abs_rtp T) (abs_rtp V) :- eval T V.
eval (rep_rtp T) V :- eval T (abs_rtp V).
