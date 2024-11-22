:- module test24.

:- interface.

:- import_module io.
:- pred main(io::di, io::uo) is det.
:- implementation.

:- import_module int.

:- pred f(int::out) is det.

:- pred r(pred int).
:- mode r(out(pred(out) is det)) is det.

:- pred r1(pred int).
:- mode r1(out(pred(out) is multi)) is det.

:- pred aux(int::out) is det.
:- pred aux1(int::out) is multi.

f(X) :- r(P), P(X).

aux(3).
r(aux). 

aux1(3).
aux1(4).

r1(aux1). 

main(!IO) :-
  f(S),
  io.write_line(S,!IO).