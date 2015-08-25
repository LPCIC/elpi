module checkers.

member X [X|_].
member X [Y|R] :- member X R.

normalize G :- term_to_string G S, G.


append nil K K.
append (X::L) K (X::M) :- append L K M.

foreach P nil.
foreach P (X::L) :- P X, foreach P L.

forsome P (X::L) :- P X; forsome P L.

memb_and_rest X (X::L) L.
memb_and_rest X (Y::K) (Y::L) :- memb_and_rest X K L.

reverse L K :- rev L nil K.
rev nil L L.
rev (X::L) K M :- rev L (X::K) M.

foldl P nil X X.
foldl P (Z::L) X Y :- P Z X W, foldl P L W Y.

length [] 0.
length (X::Q) N :- length Q N', N is N' + 1.

% Entry point
entry_point Cert Form :-
  check Cert (unfK [Form]).

%%%%%%%%%%%%%%%%%%
% Structural Rules
%%%%%%%%%%%%%%%%%%

% decide
check Cert (unfK nil) :-
  decide_ke Cert Indx Cert',
  inCtxt Indx P,
  isPos P,
  check Cert' (foc P).
% release
check Cert (foc N) :-
  isNeg N,
  release_ke Cert Cert',
  check Cert' (unfK [N]).
% store
check Cert (unfK [C|Rest]) :-
  (isPos C ; isNegAtm C),
  store_kc Cert C Indx Cert',
  inCtxt Indx C => check Cert' (unfK Rest).
% initial
check Cert (foc (p A)) :-
  initial_ke Cert Indx,
  inCtxt Indx (n A).
% cut
check Cert (unfK nil) :-
  cut_ke Cert F CertA CertB,
  negateForm F NF,
  check CertA (unfK [F]),
  check CertB (unfK [NF]).

%%%%%%%%%%%%%%%%%%%%
% Asynchronous Rules
%%%%%%%%%%%%%%%%%%%%

% orNeg
check Cert (unfK [A !-! B | Rest]) :-
  orNeg_kc Cert (A !-! B)  Cert',
  check Cert' (unfK [A, B| Rest]).
% conjunction
check Cert (unfK [A &-& B | Rest]) :-
  andNeg_kc Cert (A &-& B) CertA CertB,
  check CertA (unfK [A | Rest]),
  check CertB (unfK [B | Rest]).
% forall
check Cert (unfK [all B | Theta]) :-
  all_kc Cert Cert',
  pi w\ normalize (check (Cert' w) (unfK [B w | Theta] )).
% Units
check Cert (unfK [t-|_]). % No clerk - justify in the paper ?
check Cert (unfK [f-|Gamma]) :-  % Fix the name, between Theta, Teta, Gamma !
  false_kc Cert Cert',
  check Cert' (unfK Gamma).
% delay
check Cert (unfK [d- A| Teta]) :-
  check Cert (unfK [A| Teta]).

%%%%%%%%%%%%%%%%%%%
% Synchronous Rules
%%%%%%%%%%%%%%%%%%%
% conjunction
check Cert (foc (A &+& B)) :-
   andPos_k Cert (A &+& B) Direction CertA CertB,
   ((Direction = left-first,
   check CertA (foc A),
   check CertB (foc B));
   (Direction = right-first,
    check CertB (foc B),check CertA (foc A))).
% disjunction
check Cert (foc (A !+! B)) :-
  orPos_ke Cert (A !+! B) Choice Cert',
  ((Choice = left,  check Cert' (foc A));
   (Choice = right, check Cert' (foc B))).
% quantifers
check Cert (foc (some B)) :-
  some_ke Cert T Cert',
  eager_normalize (B T) C, % required as Teyjus doesnt normalize it before pattern matching.
  check Cert' (foc (C)).
% Units
check Cert (foc t+) :-
  true_ke Cert.
% delay
check Cert (foc (d+ A)) :-
  check Cert (foc A).

%%%%%%%%%%%
% Utilities
%%%%%%%%%%%

eager_normalize A B :- A = B.

isNegForm (_ &-& _).
isNegForm (_ !-! _).
isNegForm (d- _).
isNegForm (all _).
isPosForm (_ &+& _).
isPosForm (d+ _).
isPosForm (_ !+!  _).
isNegAtm (n _).
isPosAtm (p _).
isPosForm (some _).
isPosForm t+.
isPosForm f+.
isNegForm f-.
isNegForm t-.
isNeg A :- isNegForm A ; isNegAtm A.
isPos A :- isPosForm A ; isPosAtm A.
isPosUM A :- isPos A ; isNegAtm A.

negateForm f- t+.
negateForm t+ f-.
negateForm t- f+.
negateForm f+ t-.

negateForm (p A) (n A).
negateForm (n A) (p A).
negateForm (A &+& B)  (NA !-! NB) &
negateForm (A !-! B)  (NA &+& NB) &
negateForm (A &-& B)  (NA !+! NB) &
negateForm (A !+! B)  (NA &-& NB) :- negateForm A NA, negateForm B NB.
negateForm (all B)  (some NB) &
negateForm (some B) (all NB) :- pi x\ negateForm (B x) (NB x).


/* Temporary : for backwards compatibility.
Once the andPos_ke has been changed everywhere, andPos_k can be changed to andPos_ke,
for now andPos_k calls on andPos_ke.
*/

andPos_k Cert (A &+& B) left-first CertA CertB :-
   andPos_ke Cert (A &+& B) CertA CertB.

% Proving the sequent can be proved by deciding clauses C1, C2 and some other clause.

store_kc (dlist C1 C2) _ lit (dlist C1 C2).
store_kc (dlist2 C1) _ lit (dlist2 C1).
store_kc dlist3 _ lit dlist3.
andPos_ke (dlist C1 C2) _  (dlist C1 C2) (dlist C1 C2).
andPos_ke (dlist2 C1) _  (dlist2 C1) (dlist2 C1).
andPos_ke dlist3 _  dlist3 dlist3.
orNeg_kc (dlist C1 C2) _  (dlist C1 C2).
orNeg_kc (dlist2 C1) _  (dlist2 C1).
orNeg_kc dlist3 _  dlist3.
initial_ke (dlist _ _) _.
initial_ke (dlist _ _) _.
initial_ke (dlist2 _) _.
initial_ke dlist3 _.
initial_ke done _.
release_ke (dlist C1 C2) (dlist C1 C2).
release_ke (dlist2 C1) (dlist2 C1).
release_ke dlist3 dlist3.
% here we decide the clauses for proving -C1,-C2,C3 of decide depth 3.
% Note that since they might be negative, we will need sometimes to decide on the cut formula
% This cut formula is indexed by lit but all other resolvents from previous
% steps are indexed by idx, so we need to either decide on C1, C2 or lit
decide_ke (dlist (rid I) C2) I (dlist2 C2).
decide_ke (dlist C1 (rid I)) I (dlist2 C1).
decide_ke (dlist C1 C2) lit (dlist2 C1).
decide_ke (dlist C1 C2) lit (dlist2 C2).
decide_ke (dlist2 (rid I)) I dlist3.
decide_ke (dlist2 _) lit dlist3.
decide_ke dlist3 lit done.
% the last cut is over t+ and we need to eliminate its negation
false_kc (dlist C1 C2) (dlist C1 C2).

% gets a sequent |- A !-! B, C, D !-! E, etc.

%binary rules, use the right indices and the right resolution certificate
% eprover doesnt distinct between the from and into clauses so we try both directions
cut_ke (rsteps [PM | RS] St) K C1 C2 :-
  param_rule PM I1 I2 I,
  cut_ke (rsteps [ resolv (pid (idx I1)) (pid (idx I2)) I | RS] St) K C1 C2. % paramodulation step
cut_ke (rsteps [PM | RS] St) K C1 C2 :-
  param_rule PM I1 I2 I,
  cut_ke (rsteps [ resolv (pid (idx I2)) (pid (idx I1)) I | RS] St) K C1 C2. % paramodulation step


%unary rules, just track the indices

%ignore rules
cut_ke (rsteps [ER | RS] S) K C1 C2 :-
  ignore_rule ER,
  cut_ke (rsteps RS S) K C1 C2.
decide_ke (rsteps [ER | RS] S) A B :-
  ignore_rule ER,
  decide_ke (rsteps RS S) A B.
store_kc (rsteps [ER | RS] S) A B C :-
  ignore_rule ER,
  store_kc (rsteps RS S) A B C.

param_rule (pm (id (idx I1)) (id (idx I2)) I) I1 I2 I.
param_rule (rw (id (idx I1)) (id (idx I2)) I) I1 I2 I.
ignore_rule (cn (id (idx I1)) I2).


/*
To avoid adding the rewrit axioms everywhere, I add them here, and "include" them in every paramX.
*/
/* For debugging*/
type blurt A -> o.
blurt PM :-
term_to_string PM Str, print Str, print "\n".


inCtxt eqI (some S\ some T\ (n (S == T) &+& (p (S =*= T) !+! p (T =*= S)))).
inCtxt congI (some F\ some X\ some Y\ n (X =*= Y) &+& p (F X =*= F Y)).
inCtxt congI (some F\ some X\ some Y\ some Z\ n (X =*= Y) &+&
                                                  (p (F X Z =*= F Y Z) !+!
					     	   p (F Z X =*= F Z Y))).
inCtxt congI (some F\ some X\ some Y\ some Z\ some X'\
       	     	      	      	       n (X =*= X') &+&
                                                  (p (F X Y Z =*= F X' Y Z) !+!
					     	   p (F Y X Z =*= F Y X' Z) !+!
					     	   p (F Y Z X =*= F Y Z X'))).
/*Ciurrent changing :
Having a negative as a right-most will not do when the cert associated is doneWith.
So predI is split. predI' is created. The latter has a negative as a rightmost and
a cert that releases-stores the NEGATIVE atom and decides on resI (instead of doneWithing it)
*/
inCtxt predI (some S\ some T\ some T'\
       	     	   n (T =*= T')  &+& (n (S == T) &+& p (S == T')
		     	    	    !+!
				     n (T == S) &+& p (T' == S)
				    !+!
				     n (T == S) &+& p (S == T')
		     	    	    !+!
				     n (S == T) &+& p (T' == S)

)).
inCtxt predI' (some S\ some T\ some T'\
       	     	   n (T =*= T')  &+& (p (S == T) &+& n (S == T')
		     	    	    !+!
				     p (T == S) &+& n (T' == S)
				    !+!
				     p (T == S) &+& n (S == T')
		     	    	    !+!
				     p (S == T) &+& n (T' == S)
)).

inCtxt pred4reflI (some S\ some T\
       	     	   n (T =*= S)  &+& p (S == T)).

/*
inCtxt pred4reflI (some S\ some T\ some T'\
       	     	   (n (T =*= T')  &+& p (S == T)) &+& n (S == T')
		     	    	    !+!
		   (n (T =*= T')  &+&  p (T == S)) &+& n (T' == S)
				    !+!
		   (n (T =*= T')  &+&  p (T == S)) &+& n (S == T')
		     	    	    !+!
		   (n (T =*= T')  &+&   p (S == T)) &+& n (T' == S)
).
*/


%inCtxt reflI (some S\ p (S == S)).
inCtxt symI (some S\ some T\  n (S == T) &+& p (T == S)).

/*If the rightmost atom is negative, already know that which of the equalities is used
Have to FIRST decide on the Into (to stripp off existentials and get to the atom */
%decide_ke (dlist (pid Into) (pid From)) Into (useC From).
decide_ke (dlist (pid From) (pid Into)) Into (useC From).
release_ke (useC From) (useC From).
store_kc (useC From) _ intoI (useC From).
/*At this point, the "into" negative atom is stored under "intoI" index, we know it's negative so decide on the second predI'*/
decide_ke (useC From) predI' ((rewC From 0) c>> ((doneWith intoI) c>> posResC)).
release_ke posResC posResC.
store_kc posResC _ lastI posResC.
decide_ke posResC resI (doneWith lastI).
/* Or at this point, we should invoke the reflexivty*/
decide_ke (useC From) pred4reflI ((rewC From 0) c>> (doneWith intoI)).

/* Bureau in order of appearance*/
false_kc C C.
all_kc (dlist (pid From) (pid Into)) (x\ dlist (pid From) (pid Into)).
store_kc (dlist (pid From) (pid Into)) _ resI (dlist (pid From) (pid Into)).
%decide_ke (dlist (pid From) (pid Into)) predI ((rewC From 0) c>>  ((decOn Into)  c>> (doneWith resI))).
decide_ke (dlist (pid From) (pid Into)) predI ((rewC Into 0) c>>  ((decOn From)  c>> (doneWith resI))).
andPos_k (Cl c>> Cr) _ right-first Cl Cr.
andPos_k (Cl c<< Cr) _ left-first Cl Cr.
/*rightest branch*/
initial_ke (doneWith I) I.
/*middle branch*/
release_ke (decOn Into) (decOn Into).
store_kc (decOn Into) _ intoI (decOn Into).
decide_ke (decOn Into) Into (doneWith intoI).
	  	 % Then initial already defined
/*leftest branch : the rewrite */
release_ke (rewC From I) (rewC From I).
store_kc (rewC From I) _ (chainI I') (rewC From I') :- I' is I + 1.
/*either :*/ decide_ke (rewC From I) eqI ((fromC From) c<< (doneWith (chainI I))).
   	     release_ke (fromC I) (fromC I).
	     store_kc (fromC I) _ fromI (fromC I).
	     decide_ke (fromC I) I (doneWith fromI).
/* or    :*/decide_ke (rewC From I) congI (witC ((rewC From I) c>> (doneWith (chainI I)))).
             some_ke (witC C) FunctionSymbol C :- inSig FunctionSymbol.
	     orPos_ke C _ _ C :- (C = (doneWith I)) ; (C = (_ c>> _)).

/*Common (maybe move the initial_ke here*/
some_ke C V C :- ((C = (_ c<< _)) ; (C = (_ c>> _)) ; (C = (doneWith _));
	      	 (C = (lastC _)); (C = (reflC _)); (C = (useC _))).

/* Last of last of back bone of cuts : no rewrite, just instanciation. One of them is necessarily a negative
atom (otherwise, not stored)
We can say " From is the positive and into is the negative"
Then we are able to remove one of the following */

decide_ke (dlist (pid From) (pid Into)) From (doneWith Into).
%decide_ke (dlist (pid From) (pid Into)) Into (doneWith From).
/* Or, if using symmetry at the end */
decide_ke (dlist (pid From) (pid Into)) symI (decOn Into c>> doneWith From).
%decide_ke (dlist (pid From) (pid Into)) symI (decOn From c>> doneWith Into).

/*  Or, if the last one is not a negative atom but an existentially closed negative atom. Have to rip off the existentials first*/
decide_ke (dlist (pid From) (pid Into)) From (lastC Into).
decide_ke (dlist (pid From) (pid Into)) Into (lastC From).

release_ke (lastC From) (lastC From).
store_kc (lastC From) _ lastI (dlist (pid From) (pid lastI)).

/* Or if the last atom is not false but is violating equality's refl :
release_ke (doneWith I) (reflC I).
store_kc (reflC I)  _  lastI (reflC I).
decide_ke (reflC I) reflI (doneWith lastI).
*/

% gets a sequent |- A &+& B, C, D &+& E, etc.

% do we need it here?
release_ke (rsteps A B) (rsteps A B).
% breaking the !-! in the formula
orNeg_kc (rsteps A B) _  (rsteps A B).
% storing when the index is not given and therefore, not used by experts
% storing true (last cut)
store_kc (rsteps [] B) t+ tlit (rsteps [] B).
% storing the operands of the !-!
store_kc (rsteps A estate) C (idx I) (rsteps A estate) :-
  mapsto I C.
% the same but using given indices for storing the operands
store_kc (rsteps A (istate [I|IL])) C (idx I) (rsteps A (istate IL)).
store_kc (rsteps A _) C (idx I) (rsteps A _). % storing all other none-indexed formulas

cut_ke A B C D :- fail. % this is required due to a bug in Teyjus where no backtracking is performed when a relation is defined in two different files. Backtracking is performed when we add this fail.
cut_ke (rsteps [resolv I J K] B) f- (dlist I J) (rsteps [] B) :-
  mapsto K t+.
% Cuts correspond to resolve steps except for the last resolve
cut_ke (rsteps [(resolv I J K),R1 | RR] B) NC (dlist I J) (rsteps [R1|RR] B):-
  mapsto K CutForm,
 negateForm CutForm NC. %we would like to do the dlist on the left and also to input the resolvent as cut formulas, therefore we must negateForm it.


% this decide is being called after the last cut
decide_ke (rsteps [] B) tlit done.
true_ke (done).

parseInput [(pr I Cl)] f- [] NCl [I] :-
  negateForm Cl NCl.

parseInput [(pr I Cl) | Ls] F Il (NCl !-! F2) [I | Il2] :-
  parseInput Ls F Il F2 Il2,
  negateForm Cl NCl.

negateMap [] [].
negateMap [(pr I Cl) | Map] [(pr I NCl) | Map2] :-
  negateForm Cl NCl,
  negateMap Map Map2.

run :-
  resProblem Name Ls (resteps C) (map Map),
  parseInput Ls f- [] F Istate,
  print "Running on problem ", print Name, print ":\n",
  negateMap Map Map2,
  resolve Map2 F (rsteps C (istate Istate)).

run :-
  problem Name F Cert (map Map),
  print "Running on problem ", print Name, print ":\n",
  resolve Map F Cert.

resolve [] F Cert :-
  if (entry_point Cert F)
      (print "Success\n==============================================\n")
		  (print "Fail\n", halt), fail.
resolve [(pr I C) | R] F Cert :-
  mapsto I C => resolve R F Cert.

resProblem "col060" [(pr 8 (all (X1\ (all (X2\ (n ((apply (apply t X1) X2) == (apply X2 X1))))))) ),
(pr 7 (all (X1\ (all (X2\ (all (X3\ (n ((apply (apply (apply b X1) X2) X3) == (apply X1 (apply X2 X3)))))))))) ),
(pr 6 (all (X1\ (p ((apply (apply (apply X1 (f X1)) (g X1)) (h X1)) == (apply (g X1) (apply (f X1) (h X1))))))) )] 
(resteps [pm (id (idx 6)) (id (idx 7)) 5, pm (id (idx 5)) (id (idx 8)) 4, pm (id (idx 4)) (id (idx 7)) 3, pm (id (idx 3)) (id (idx 7)) 2, pm (id (idx 2)) (id (idx 8)) 1, pm (id (idx 1)) (id (idx 7)) 0])
 (map [
pr 4 (all (X2\ (all (X1\ (p ((apply (apply (apply (apply X2 (f (apply (apply b (apply t X1)) X2))) X1) (g (apply (apply b (apply t X1)) X2))) (h (apply (apply b (apply t X1)) X2))) == (apply (g (apply (apply b (apply t X1)) X2)) (apply (f (apply (apply b (apply t X1)) X2)) (h (apply (apply b (apply t X1)) X2)))))))))),
pr 7 (all (X1\ (all (X2\ (all (X3\ (n ((apply (apply (apply b X1) X2) X3) == (apply X1 (apply X2 X3)))))))))),
pr 0 f-,
pr 1 (all (X1\ (p ((apply (apply (apply X1 (g (apply (apply b (apply t X1)) (apply (apply b b) t)))) (f (apply (apply b (apply t X1)) (apply (apply b b) t)))) (h (apply (apply b (apply t X1)) (apply (apply b b) t)))) == (apply (g (apply (apply b (apply t X1)) (apply (apply b b) t))) (apply (f (apply (apply b (apply t X1)) (apply (apply b b) t))) (h (apply (apply b (apply t X1)) (apply (apply b b) t))))))))),
pr 8 (all (X1\ (all (X2\ (n ((apply (apply t X1) X2) == (apply X2 X1))))))),
pr 6 (all (X1\ (p ((apply (apply (apply X1 (f X1)) (g X1)) (h X1)) == (apply (g X1) (apply (f X1) (h X1))))))),
pr 2 (all (X1\ (all (X2\ (p ((apply (apply (apply X1 (f (apply (apply b (apply t X2)) (apply (apply b b) X1)))) (apply X2 (g (apply (apply b (apply t X2)) (apply (apply b b) X1))))) (h (apply (apply b (apply t X2)) (apply (apply b b) X1)))) == (apply (g (apply (apply b (apply t X2)) (apply (apply b b) X1))) (apply (f (apply (apply b (apply t X2)) (apply (apply b b) X1))) (h (apply (apply b (apply t X2)) (apply (apply b b) X1))))))))))),
pr 3 (all (X1\ (all (X2\ (all (X3\ (p ((apply (apply (apply (apply X1 (apply X2 (f (apply (apply b (apply t X3)) (apply (apply b X1) X2))))) X3) (g (apply (apply b (apply t X3)) (apply (apply b X1) X2)))) (h (apply (apply b (apply t X3)) (apply (apply b X1) X2)))) == (apply (g (apply (apply b (apply t X3)) (apply (apply b X1) X2))) (apply (f (apply (apply b (apply t X3)) (apply (apply b X1) X2))) (h (apply (apply b (apply t X3)) (apply (apply b X1) X2))))))))))))),
pr 5 (all (X1\ (all (X2\ (p ((apply (apply (apply X1 (apply X2 (f (apply (apply b X1) X2)))) (g (apply (apply b X1) X2))) (h (apply (apply b X1) X2))) == (apply (g (apply (apply b X1) X2)) (apply (f (apply (apply b X1) X2)) (h (apply (apply b X1) X2))))))))))
]).

inSig h.
inSig apply.
inSig g.
inSig f.

if P Q R :- P, !, Q.
if P Q R :- R.

main :- run.
