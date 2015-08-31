module paramodulation.


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

