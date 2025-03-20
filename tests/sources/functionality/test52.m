:- module testTODO1.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module int.
:- import_module list.

:- pred divisor_help(int::in,int::in,int::out) is nondet.
divisor_help(N,N,N).
divisor_help(N,M,N) :- M mod N = 0.
% divisor_help(N,M,R) :- N < M, N1 = N + 1, divisor_help N1 M R.

:- pred divisor(int::in,int::out) is nondet.
divisor(N, M):- divisor_help(1,N,M).

:- pred mmap(pred(X, Y), list(X), list(Y)).
:- mode mmap(in(pred(in, out) is det), in, out) is det.
:- mode mmap(in(pred(in, out) is cc_multi), in, out) is cc_multi.
:- mode mmap(in(pred(in, out) is semidet), in, out) is semidet.
:- mode mmap(in(pred(in, out) is multi), in, out) is multi.
:- mode mmap(in(pred(in, out) is nondet), in, out) is nondet.
:- mode mmap(in(pred(in, in) is semidet), in, in) is semidet.
:- mode mmap(in(pred((pred(out) is nondet),out) is nondet),in,out) is nondet.
% :- mode mmap(in(pred((pred(out) is nondet),out) is nondet),in(pred((pred(out) is nondet),out) is nondet),out) is nondet.

mmap(_, [],  []).
mmap(P, [H0 | T0], [H | T]) :-
    P(H0, H),
    mmap(P, T0, T).


:- pred give_fun(list(list(int))::out) is nondet.
give_fun(L) :-
  Pred = (pred(F::(pred(out) is nondet),I::out) is nondet :- F(I)),
  % Pred = (pred(F::in,I::out) is nondet :- F(I)),
  mmap(Pred,[mmap(divisor,[2,9])],L).

main(!IO).
