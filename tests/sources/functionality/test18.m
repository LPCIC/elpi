:- module test18.

:- interface.

:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.

:- pred q(int::out) is multi.
q(0).
q(1).

:- pred do(pred).
:- mode do(in((pred) is det)) is det.

do(P) :- P.

:- pred x(int::out) is det.

x(Y) :- do(q(Y)).

main(!IO) :-
  io.write_line(10,!IO).

% cd out && clear && mmc ../tests/sources/functionality/test18.m 

