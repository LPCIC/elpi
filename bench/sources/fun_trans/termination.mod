module termination.

accumulate part_eval.

type reaches_mnont tm -> o.

converges T1 :-
  part_eval T1 T2,
  !,
  not (reaches_mnont T2).

reaches_mnont (let_comp _T F) :- pi x\ reaches_mnont (F x).
reaches_mnont (let_mnont _T _F).
