%  This module illustrates the encoding of Hilbert's Tenth Problem into
%  the problem of determining if flexible-flexible disagreement pairs
%  have *closed* solutions when not all types are know to be empty.
%  For the correctness proof of this encoding, see
%  
%    D. Miller, ``Unification under a mixed prefix'', Journal of
%    Symbolic Computation, volume 14, 321-358 (1992).
%  
%  The reduction used here is similar to the one found in 
%  
%    W. Goldfarb, ``The Undecidability of the Second-Order
%    Unification Problem,'' Theoretical Computer Science 13, 1981,
%    225 -- 230.
%
%  Notice that lambda Prolog cannot be used to actually solve the
%  encoded problems since all the computation gets done in
%  flexible-flexible pairs, which are not processed much in lambda Prolog.
%  This file is useful in only showing the reduction to flex-flex
%  pairs.

module hilbert.

kind  i  type.

%  Notice that there are no constructors for objects in type i.  This
%  allows you to conclude that the only closed terms of 
%                          (i -> i) -> (i -> i) 
%  are the Church numerals.

type  zero, one, church     ((i -> i) -> (i -> i)) -> o.

type  plus, mult
       (((i -> i) -> i -> i) -> ((i -> i) -> i -> i) ->
        ((i -> i) -> i -> i)) -> o.
type  succ  (((i -> i) -> i -> i) -> ((i -> i) -> i -> i)) -> o.

type  problem1   ((i -> i) -> i -> i) ->  ((i -> i) -> i -> i) -> 
                 ((i -> i) -> i -> i) ->  ((i -> i) -> i -> i) -> o.

%  Three combinators for Church arithmetic.  succ is not needed given
%  plus, but it's convenient.

succ    (N\F\X\ (N F (F X))).
plus  (N\M\F\X\ ((N F) (M F X))).
mult  (N\M\F\X\ (N (M F) X)).

%  The definitions for Church numerals below are not used in the
%  encoding.  They are included just for convenience.  They are not used
%  since they contribute flexible-rigid pairs: only flexible-flexible
%  pairs are wanted.

church (F\X\ X).
church (F\X\ (C F (F X))) :- church C.

%  Here is how to describe zero and one using flexible-flexible pairs.

%  zero is the only solution to the equation
%    z = z + z
zero Z :- plus P, Z = (P Z Z).

%  one is the only solution to the equation
%    z + z = z + 1
one O  :- plus P, succ S, (P O O) = (S O).

%  Now, encode the following set of equations:
%     { x = 1, u = x + x,  x + y = z, y * z = u }
%  This set has exactly one solution:  x = 1, u = 2, y = 1, z = 2.

problem1 X U Y Z :-
  one O, plus P, mult M,
  X = O, U = (P X X), Z = (P X Y), U = (M Y Z).


%  ?- zero Z.
%  
%  Z = Z
%  
%   The remaining flexible - flexible pairs:
%  <Z , F \ X \ (Z F (Z F X))>.
%   yes

%  ?- one Z.
%  
%  Z = Z
%  
%   The remaining flexible - flexible pairs:
%  <F \ X \ (Z F (Z F X)) , F \ X \ (Z F (F X))>.
%   yes

%  This is the result of problem 1 using LP2.6.  If only closed terms are
%  allowed for Var1 and Var6, then both of these must be the Church
%  numeral 1 to satisfy the flexible-flexible pairs below.  The bound
%  variables names were changed to make this example more readable.
%
%  ?- problem1 U V W Y.
%  
%  U = Var1,
%  V = F \ X \ (Var1 F (Var1 F X)),
%  W = Var6,
%  Y =  F \ X \ (Var1 F (Var6 F X))
%  
%   The remaining flexible - flexible pairs:
%  <F \ X \ (Var1 F (Var1 F X)),
%   F \ X \ (Var6 Y \ (Var1 F (Var6 F Y)) X)>
%  <F \ X \ (Var1 F (Var1 F X)),
%   F \ X \ (Var1 F (F X))>.

%  Notice that using the predicate church, we can attempt to solve these
%  equational systems using a naive generate and test stradegy.  In the
%  following example, the flexible-flexible pairs for constraints which
%  are tested against successive integers.
%  
%  ?- problem1 X U Y Z, church U.
%  
%  X = F \ X \ (F X)
%  Y = F \ X \ (F X)
%  Z = F \ X \ (F (F X))
%  U = F \ X \ (F (F X))
%  
%  This is a pretty silly way to solve such equations in practice.


% Added by Liang for testing teyjus:
% converts ints to church numerals
cn 0 Z :- zero Z.
cn 1 One :- one One.
cn N (P CNP One) :- N > 1, NP is (N - 1), plus P, one One, cn NP CNP.

% tests:
% 4 + x = 6 :
test 1 :- plus P, cn 4 C4, cn 6 (P C4 X).
% x * 5 = 20 :
test 2 :- mult M, cn 5 C5, cn 20 (M X C5).
% x * 6 + 5 = 41 
test 3 :- mult M, plus P, cn 6 C6, cn 5 C5, cn 41 (P (M X C6) C5).
% x * 3 = y, y + y = x   
test 4 :- mult M, plus P, cn 3 C3, Y = (M X C3), X = (P Y Y),
          zero X, zero Y.
% (a * a) + (b * b) = c * c
test 5 :- mult M, plus P, (P (M A A) (M B B)) = (M C C).

% The above tests didn't produce much

test 6 :-   cn 20 N, X = (P N (P N N)).  % more interesting
test 7 :-   cn 10 N, cn 105 (P (M N N) FIVE).


go :- test X, fail.
go :- stop. 

main :- test X.

 
% cn 500 N will cause "Term free variable name table is full."
% teyjus tests made with cn 200.




