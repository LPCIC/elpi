:- module test16.

:- interface.

:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.

:- pred p(int::in, int::out) is semidet.
:- pred f(int::out, int::out, int::out) is multi.

f(1,2,3).
f(2,3,1).
f(1,3,2).

p(4, Y) :- f(_Z,_X,_W), Y = 4.

% ERROR: this makes the predicate non-det:
% we may need to do backtracking in the body of p
p(5, 3) :- f(Z,X,T), f(X,Z,T).

main(!IO) :-
  io.write_line(10,!IO).

% clear && mmc ../tests/sources/functionality/test1.m 