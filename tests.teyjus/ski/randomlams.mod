module randomlams.

% assume random R X. will get a random number between 0 and R-1.
% 0 - free variable
% 1 - bound variable
% 2 - app term
% 3 - abs term


% free var
genterm 0 BV (freevar X).

% bound var
genterm 1 [] (freevar V) :- !.   % defaults to free variable.
genterm 1 BV V :-
  length BV L, random L N,
  nthmemb N BV V.

% app term 
genterm 2 BV (app A B) :- 
  random 4 N, random 4 M,
  genterm N BV A, genterm M BV B.

% abs term
genterm 3 BV (abs A) :- 
  random 4 N,
  (pi v\ (genterm N (v::BV) (A v))).


% object-level head normalization
%hnorm A B :- printterm std_out (hnorm A B), print " <-\n", fail.
%hnormw A B :- printterm std_out (hnormw A B), print " <-\n", fail.

hnorm (freevar V) (freevar V).
hnorm X Y :- bvar X, X = Y.
%hnorm X X :- bvar X.
hnorm (abs A) (abs B) :- pi v\ (bvar v => hnorm (A v) (B v)).
hnorm (app A B) C :- hnormw A D,  
    ((D = (abs D2), hnorm (D2 B) C); 
     (app D B) = C), !.

%local hnormaux, hnormwaux i -> i -> i -> o.
%hnormaux (abs D2) B C :- !, hnorm (D2 B) C.
%hnormaux D B (app D B).

hnormw (freevar V) (freevar V).
hnormw X Y :- bvar X, X = Y.
%hnormw X X :- bvar X.
hnormw (abs A) (abs A).
hnormw (app A B) C :- hnormw A D, 
    ((D = (abs D2), hnormw (D2 B) C); 
     (app D B) = C), !.

% (abs x\ (app (app (abs y\ (abs z\ y)) (app x x)) x)). 
%hnormwaux (abs D2) B C :- !, hnormw (D2 B) C.
%hnormwaux D B (app D B).



% generate lambda terms 
% (go N) generates N random lambda terms

go Max:- 
  open_socket "127.0.0.1" 1917 In Out,
    (instream In => (outstream Out => go2 Max)),
  output Out "bye\n", 
  close_in In, close_out Out.


% this algorithm tries to cut down on the number of single freevar terms:
go2 0.
go2 M :- M > 0, random 2 N, N2 is (N + 2), genterm N2 [] T, 
   print "lambdaterm (", printterm std_out T, print ").\n", 
   M2 is (M - 1), go2 M2.
      
randterm T :-
  open_socket "127.0.0.1" 1917 In Out, 
  (instream In => (outstream Out => 
	( random 6 N, genterm N [] T))),
  output Out "bye\n", flush Out,
  close_in In, close_out Out.


random Range Num :-
  instream In, outstream Out,
  RS is (int_to_string Range),
  output Out RS, output Out "\n", flush Out,
  input_line In Ins,
  open_string Ins STIN,
  readterm STIN Num, 
  close_in STIN.

%  Rand is (string_to_int Ins), Num is (Rand - 48), Num < 10, Num >= 0.
% The more general way (the above option only gets one-digit values):
%  open_string Ins STIN,
%  readterm STIN Num, 
%  print "Got number: ", printterm std_out Num, print "\n",
%  close_in STIN. 



%  ---  utilities.    

length [] 0.
length [H|T] N :- length T M, N is (M + 1).

nthmemb 0 [H|T] H.
nthmemb N [H|T] U :- N2 is (N - 1), nthmemb N2 T U.




% -----  pure combinators

combinator 0 "I" (abs x\x).
combinator 1 "K" (abs x\ (abs y\x)).
combinator 2 "S" (abs x\ (abs y\ (abs z\ (app (app x z) (app y z))))). 

% R>2  controls how often terms are the primitives
combinator R Str (app A B) :- R > 2,
        Rp is (R + 1),
	random Rp R1, random Rp R2,
	combinator R1 S1 A, combinator R2 S2 B,
	Str is ( "(" ^ S1 ^ " " ^ S2 ^ ")").

% range controls complexity
randomcombo Range Str T :-
  open_socket "127.0.0.1" 1917 In Out, 
  (instream In => (outstream Out => 
	( random Range N, combinator N Str T))),
  output Out "bye\n", flush Out,
  close_in In, close_out Out.

% Range controls depth of random terms, Max is number of terms to
% be generated.  Out is name of module to be created.
makecombos Range Max Module :- 
  open_socket "127.0.0.1" 1917 In Out,
  File is (Module ^ ".mod"),
  open_out File Fout,
  output Fout "module ", output Fout Module, output Fout ".\n",
  output Fout "accumulate randomlams.\n\n",
  Sigfile is (Module ^ ".sig"), open_out Sigfile Sout,
  output Sout "sig ", output Sout Module, 
  output Sout ".\naccum_sig randomlams.\n", close_out Sout,
    (instream In => (outstream Out => mc2 Range Max Fout)),
  output Out "bye\n", 
  close_in In, close_out Out, close_out Fout.

type mc2 int -> int -> out_stream -> o.
mc2 Range M Out :- M > 0, random Range N, combinator N Str T,
   output Out "combo ", printterm Out Str, output Out " (", 
   printterm Out T, output Out ").\n", 
   M2 is (M - 1), mc2 Range M2 Out.


test :- combo Str T, hnorm T R, fail.
test.


%  ---- full normalization outside in:


fnorm (freevar V) (freevar V).
fnorm X Y :- bvar X, X = Y.
fnorm (abs A) (abs B) :- pi v\ (bvar v => fnorm (A v) (B v)).
fnorm (app A B) C :- fnormw A D,  
    ((D = (abs D2), fnorm (D2 B) C); 
     (fnorm B B2, C = (app D B2))), !.


fnormw (freevar V) (freevar V).
fnormw X Y :- bvar X, X = Y.
fnormw (abs A) (abs A).
fnormw (app A B) C :- fnormw A D, 
    ((D = (abs D2), fnormw (D2 B) C); 
     (fnorm B B2, C = (app D B2))), !.


ftest :- combo Str T, fnorm T R, fail.
ftest.

once :- test, ftest.

iter zero X.
iter (s N) X :- X, iter N X.

plus zero X X.
plus (s X) Y (s S) :- plus X Y S.

mult zero X zero.
mult (s X) Y Z :- mult X Y K, plus Y K Z.

exp zero X (s zero).
exp (s X) Y Z :- exp X Y K, mult Y K Z.

main :-
 TEN = s (s (s (s (s (s (s (s (s (s zero))))))))),
 mult (s (s (s (s zero)))) TEN FIFTY,
 iter FIFTY once.
