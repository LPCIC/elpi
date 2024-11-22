:- module test5.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module int.

:- pred p(int::in, int::out) is semidet.
:- pred q(int::in, int::out) is semidet.

q(1,1).
p(1,R) :- (all [Y] (q(2, Y) <= Y = 3)) => q(2, R).

main(!IO).