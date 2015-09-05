module utils.

type rev_mapP_aux (A -> B -> o) -> list A -> list B -> list B -> o.
type nth_aux list A -> int -> A -> o.
type flatten_aux list (list A) -> list A -> list A -> o.
type filter_aux (A -> o) -> list A -> list A -> list A -> o.
type partition_aux (A -> o) -> list A -> list A -> list A ->
                                         list A -> list A -> o.

nl :- print "\n".

println S :-
  print S,
  nl.

write T :- printterm std_out T.

writeln T :-
  printterm std_out T,
  nl.

length L N :- fold_leftP (M\ E\ N\ N is M + 1) 0 L N.

nth_aux (H::T) 0 H :- !.

nth_aux (_::T) N Res :-
  M is N - 1,
  nth_aux T M Res.

nth L N Res :-
  N >= 0,
  nth_aux L N Res.

rev L Res :- rev_append L nil Res.

rev_append nil L L.
rev_append (H::T) L Res :- rev_append T (H::L) Res.

append L1 L2 Res :-
  rev L1 RL1,
  rev_append RL1 L2 Res.

flatten_aux nil Acc Acc.

flatten_aux (H::T) Acc Res :-
  rev_append H Acc R,
  flatten_aux T R Res.

flatten L Res :-
  flatten_aux L nil RL,
  rev RL Res.

rev_mapP_aux _P nil Acc Acc.

rev_mapP_aux P (H1::T) Acc Res :-
  P H1 H2,
  rev_mapP_aux P T (H2::Acc) Res.

rev_mapP P L Res :- rev_mapP_aux P L nil Res.

mapP P L Res :-
  rev_mapP P L R,
  rev R Res.

fold_leftP _P Acc nil Acc.

fold_leftP P Acc (H::T) Res :-
  P Acc H NAcc,
  fold_leftP P NAcc T Res.

fold_rightP _P nil Acc Acc.

fold_rightP P (H::T) Acc Res :-
  fold_rightP P T Acc R,
  P H R Res.

forall _P nil.

forall P (H::T) :-
  P H,
  forall P T.

exists P (H::T) :-
    P H
  ; exists P T.

mem X (X::T) :- !.
mem X (_::T) :- mem X T.

member X (H::T) :-
    X = H
  ; member X T.

find P (H::T) Res :-
    P H,
    H = Res
  ; find P T Res.

filter_aux _P nil Acc Acc.

filter_aux P (H::T) Acc Res :-
  P H,
  !,
  filter_aux P T (H::Acc) Res.

filter_aux P (_::T) Acc Res :- filter_aux P T Acc Res.

filter P L Res :-
  filter_aux P L nil R,
  rev R Res.

partition_aux _P nil YAcc Yes NAcc No :-
  rev YAcc Yes,
  rev NAcc No.

partition_aux P (H::T) YAcc Yes NAcc No :-
  P H,
  !,
  partition_aux P T (H::YAcc) Yes NAcc No.

partition_aux P (H::T) YAcc Yes NAcc No :-
  partition_aux P T YAcc Yes (H::NAcc) No.

partition P L Yes No :- partition_aux P L nil Yes nil No.

qsort _P L L :- L = nil.

qsort P (H::T) Res :-
  partition (E\ P E H) T Yes No,
  qsort P Yes SYes,
  qsort P No SNo,
  append SYes (H::SNo) Res.

contains T ST :-
  T = F ST,
  not (pi x\ F x = T).

elim_sub_term T ST F :-
  pi x\ sigma Fx\
    F ST = T,
    Fx = F x,
    not ( Fx = T ; contains Fx ST ).

elim_sub_patterns T PGen F :-
  PGen Pat,
  pi x\ sigma Fx\ sigma H\
    G Pat = T,
    Fx = G x, 
    not ( Fx = T ; contains Fx Pat ),
    (
      elim_sub_patterns Fx PGen H,
      F x = H x
    ;
      F = G
    ).
