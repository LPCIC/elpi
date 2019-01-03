% crypt
%
% Cryptomultiplication:
% Find the unique answer to:
%	OEE    348  *
%	 EE     28  
% 	---
%      EOEE    2784  +
%      EOE     696  
%      ----   -----
%      OOEE    9744
%
% where E=even, O=odd.
% This program generalizes easily
% to any such problem.
% Written by Peter Van Roy


module crypt.

crypt ShowResult :-
	odd A , even B , even C , even E ,
	mult (xcons C (xcons B (xcons A xnil)))  E  (xcons I (xcons H (xcons G (xcons F X)))),
	lefteven F , odd G , even H , even I , zero X , lefteven D,
	mult (xcons C (xcons B (xcons A xnil)))  D  (xcons L (xcons K (xcons J Y))),
	lefteven J , odd K , even L , zero Y,
	sum2 (xcons I (xcons H (xcons G (xcons F xnil)))) (xcons null (xcons L (xcons K (xcons J xnil)))) (xcons P (xcons O (xcons N (xcons M Z)))),
	odd M , odd N , even O , even P , zero Z,
  ShowResult = xcons A (xcons B (xcons C (xcons D (xcons E (xcons F (xcons G (xcons H (xcons I (xcons J (xcons K (xcons L (xcons M (xcons N (xcons O (xcons P xnil))))))))))))))).
%	(   ShowResult = true ->
%	    write(' '), write(A), write(B), write(C), nl,
%	    write('  '), write(D), write(E), nl,
%	    write(F), write(G), write(H), write(I), nl,
%	    write(J), write(K), write(L), nl,
%	    write(M), write(N), write(O), write(P), nl
%	;   true).

% In the usual source this predicate is named sum. However, sum is a
% language construct in NU-Prolog, and cannot be defined as a predicate.
% If you try, nc comes up with an obscure error message.

sum2 AL BL CL :- sum2_aux AL BL null CL.

sum2_aux (xcons A AL) (xcons B BL) Carry (xcons C CL) :- !,	
   plus A B S,
   plus S Carry X,
	modd X (s (s (s (s (s (s (s (s (s (s null)))))))))) C,
	divv X (s (s (s (s (s (s (s (s (s (s null)))))))))) NewCarry,
	sum2_aux AL BL NewCarry CL.
sum2_aux xnil BL null BL :- !.
sum2_aux AL xnil null AL :- !.
sum2_aux xnil (xcons B BL) Carry (xcons C CL) :- !,
	plus B Carry X,
	divv X (s (s (s (s (s (s (s (s (s (s null)))))))))) NewCarry,
	modd X (s (s (s (s (s (s (s (s (s (s null)))))))))) C,
	sum2_aux xnil BL NewCarry CL.
sum2_aux (xcons A AL) xnil Carry (xcons C CL) :- !,
	plus A Carry X,
	divv X (s (s (s (s (s (s (s (s (s (s null)))))))))) NewCarry,
	modd X (s (s (s (s (s (s (s (s (s (s null)))))))))) C,
	sum2_aux xnil AL  NewCarry CL.
sum2_aux xnil xnil Carry (xcons Carry xnil).

mult AL D BL :- mult_aux AL D null BL.

mult_aux xnil _ Carry (xcons C (xcons Cend xnil)) :-
	modd Carry (s (s (s (s (s (s (s (s (s (s null)))))))))) C,
	divv Carry (s (s (s (s (s (s (s (s (s (s null)))))))))) Cend.
mult_aux (xcons A AL) D Carry (xcons B BL) :-
   prod A D S,
   plus S Carry X,
	modd X (s (s (s (s (s (s (s (s (s (s null)))))))))) B,
	divv X (s (s (s (s (s (s (s (s (s (s null)))))))))) NewCarry,
	mult_aux AL D NewCarry BL .

%%%%%%%%%%%%%%%
plus null X X.
plus (s X) Y (s S) :- plus X Y S.

prod null X null.
prod (s X) Y S :- prod X Y S1, plus Y S1 S.

modd X Y X :- less X Y.
modd X Y Z :- plus X1 Y X, modd X1 Y Z.

divv X Y null :- less X Y.
divv X Y (s D) :- plus X1 Y X, divv X1 Y D.

less null (s _).
less (s X) (s Y) :- less X Y.
%%%%%%%%%%%%%%%



zero xnil.
zero (xcons null L) :- zero L.

is_even null.
is_even (s X) :- is_odd X.
is_odd (s X) :- is_even X.
is_lefteven (s (s X)) :- is_even X.

digit X :- less X (s (s (s (s (s (s (s (s (s (s null)))))))))). 
even X :- digit X, is_even X.
odd X :- digit X, is_odd X.
lefteven X :- digit X, is_lefteven X.

% benchmark interface

once :-
	crypt X,
  check X (xcons
    (s (s (s null)))
     (xcons
       (s (s (s (s null))))
        (xcons
          (s (s (s (s (s (s (s (s null))))))))
           (xcons
             (s (s null))
              (xcons
                (s (s (s (s (s (s (s (s null))))))))
                 (xcons
                   (s (s null))
                    (xcons
                      (s (s (s (s (s (s (s null)))))))
                       (xcons
                         (s (s (s (s (s (s (s (s null))))))))
                          (xcons
                            (s (s (s (s null))))
                             (xcons
                               (s (s (s (s (s (s null))))))
                                (xcons
                                  (s (s (s (s (s (s (s (s (s null)))))))))
                                   (xcons
                                     (s (s (s (s (s (s null))))))
                                      (xcons
                                        (s
                                          (s (s (s (s (s (s (s (s null)))))))))
                                         (xcons
                                           (s (s (s (s (s (s (s null)))))))
                                            (xcons
                                              (s (s (s (s null))))
                                               (xcons
                                                 (s (s (s (s null)))) xnil)))))))))))))))).

check A A.

iter null.
iter (s N) :- once, iter N.

exp null X (s null).
exp (s X) Y Z :- exp X Y K, prod Y K Z.

main :-
 TEN = s (s (s (s (s (s (s (s (s (s null))))))))),
 exp (s (s null)) TEN HUNDRED,
 iter HUNDRED.
