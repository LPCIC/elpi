module terms.

tm_fun_linear F :-
  pi v\
    tm_linear_aux v true fail =>
      tm_linear_aux (F v) true _.

tm_linear_aux u X X :- !.

tm_linear_aux (pair T1 T2) A C :-
  !,
  tm_linear_aux T1 A B,
  tm_linear_aux T2 B C.

tm_linear_aux (fst T) A B :- !, tm_linear_aux T A B.
tm_linear_aux (snd T) A B :- !, tm_linear_aux T A B.

tm_linear_aux (inl T) A B :- !, tm_linear_aux T A B.
tm_linear_aux (inr T) A B :- !, tm_linear_aux T A B.

tm_linear_aux (case CT LF RF) A C :-
  !,
  tm_linear_aux CT A B,
  tm_fun_linear_aux LF B C1,
  tm_fun_linear_aux RF B C2,
  (
    C1,
    C = C2
  ;
    C = fail
  ).

tm_linear_aux (lam F) A B :- !, tm_fun_linear_aux F A B.

tm_linear_aux (rec F) A B :-
  !,
  pi f\
    (pi X\ tm_linear_aux f X X) =>
      tm_fun_linear_aux (F f) A B.

tm_linear_aux (app T1 T2) A C :-
  !,
  tm_linear_aux T1 A B,
  tm_linear_aux T2 B C.

tm_linear_aux (abs_rtp T) A B :- !, tm_linear_aux T A B.
tm_linear_aux (rep_rtp T) A B :- !, tm_linear_aux T A B.

tm_fun_linear_aux F A B :-
  pi x\
    (pi X\ tm_linear_aux x X X) =>
      tm_linear_aux (F x) A B.

output_tm Ch T :- printterm Ch T.

print_tm T :- output_tm std_out T.
