/*

File: constructive_logic.mod
Author: Louise Dennis / James Brotherston
Description: Theory of logic with equality
Last Modified: 20th August 2002

*/

module constructive_logic.

local atomic_term    osyn -> o.


/*
SYNTAX CONSTANTS
*/

is_otype constructive_logic bool [trueP, falseP] nil.

has_otype constructive_logic and ((tuple_type [bool, bool]) arrow bool).
has_otype constructive_logic or ((tuple_type [bool, bool]) arrow bool).
has_otype constructive_logic imp ((tuple_type [bool, bool]) arrow bool).
has_otype constructive_logic neg (bool arrow bool).
has_otype constructive_logic forall ((tuple_type [universe, (_X arrow bool)]) arrow bool).
has_otype constructive_logic exists ((tuple_type [universe, (_X arrow bool)]) arrow bool).
has_otype constructive_logic falseP bool.
has_otype constructive_logic trueP bool.
has_otype constructive_logic iff ((tuple_type [bool, bool]) arrow bool).
has_otype constructive_logic eq ((tuple_type [X, X]) arrow bool).
has_otype constructive_logic neq ((tuple_type [X, X]) arrow bool).
has_otype constructive_logic transitive (((tuple_type [X, X]) arrow bool) arrow bool).
has_otype constructive_logic xor ((tuple_type [bool, bool]) arrow bool).
% has_otype constructive_logic ifthen ((tuple_type [bool, X, X]) arrow X).

%% the OpenMath phrasebook entries for the constants:
%%==================================================
print_open_math_ and    "'OMS'(name:\"and\" cd:\"logic1\")".
print_open_math_ or     "'OMS'(name:\"or\" cd:\"logic1\")".
print_open_math_ imp    "'OMS'(name:\"implies\" cd:\"logic1\")".
print_open_math_ neg    "'OMS'(name:\"not\" cd:\"logic1\")".
print_open_math_ forall "'OMS'(name:\"forall\" cd:\"quant1\")".
print_open_math_ exists "'OMS'(name:\"exists\" cd:\"quant1\")".
print_open_math_ falseP "'OMS'(name:\"false\" cd:\"logic1\")".
print_open_math_ trueP  "'OMS'(name:\"true\" cd:\"logic1\")".
print_open_math_ iff    "'OMS'(name:\"equivalent\" cd:\"logic1\")".
print_open_math_ eq     "'OMS'(name:\"eq\" cd:\"relation1\")".
print_open_math_ neq    "'OMS'(name:\"neq\" cd:\"relation1\")".
print_open_math_ xor    "'OMS'(name:\"xor\" cd:\"logic1\")".

% logic1 CD: and, equivalent, false, implies, not, or, true, xor 
% relation1 CD: approx, eq, geq, gt, leq, lt, neq 

%%================================================

/* DEFINITIONS AND LEMMAS */

definition constructive_logic neq_eval trueP
     (app neq (tuple [X, Y])) (
     app neg (app eq (tuple [X, Y]))).

/* maybe this should be a definition ? */
lemma constructive_logic idty equiv trueP (app eq (tuple [X, X])) trueP.

/* truth tables */
definition constructive_logic neg1 trueP (app neg trueP) falseP.
definition constructive_logic neg2 trueP (app neg falseP) trueP.
definition constructive_logic and1 trueP (app and (tuple [falseP, _])) falseP.
definition constructive_logic and2 trueP (app and (tuple [_, falseP])) falseP.
definition constructive_logic or1 trueP (app or (tuple [trueP, _])) trueP.
definition constructive_logic or2 trueP (app or (tuple [_, trueP])) trueP.
definition constructive_logic imp1 trueP (app imp (tuple [falseP, _])) trueP.
definition constructive_logic imp2 trueP (app imp (tuple [_, trueP])) trueP.

/* ? should these count as definitions ? */

lemma constructive_logic or3 equiv trueP (app or (tuple [falseP, X])) X.

lemma constructive_logic iff1 equiv trueP (app iff (tuple [trueP, X])) X.

/* OTHER LEMMAS */

lemma constructive_logic assAnd1 equiv trueP (app and (tuple [A, (app and (tuple [B, C]))])) 
                              (app and (tuple [(app and (tuple [A, B])), C])).

lemma constructive_logic prop3 equiv trueP  (app and (tuple [A, (app and (tuple [B, C]))])) 
                             (app and (tuple [B, (app and (tuple [A, C]))])).
lemma constructive_logic prop5 equiv trueP
   (app imp  
    (tuple [A,
           (app and (tuple [A, B]))])) 
   (app imp (tuple [A, B])).

lemma constructive_logic prop6 equiv trueP (app or (tuple [A, (app and (tuple [B, C]))])) 
                            (app and (tuple [(app or (tuple [A, B])),
                                             (app or (tuple [A, C]))])).

% Probably shouldn't be here but don't know where else to put it.
% Abusing polarity here and using it to control rewriting.

axiom constructive_logic beta_reduction equiv
	trueP
	(app (abs x\ (F x)) Y)
	(F Y).

axiom constructive_logic beta_idty equiv
	trueP
	(app eq (tuple [Y, (app (abs x\ x) Y)]))
	trueP.

lemma constructive_logic prop4 rtol trueP
    (app imp (tuple [(app and (tuple [A, B])), (app and (tuple [A, C]))])) 
    (app imp (tuple [B, C])).


% ifthen
%
definition constructive_logic ifthen1 C (app ifthen (tuple [C, X, _])) X.
definition constructive_logic ifthen1 (app neg C)
	(app ifthen (tuple [C, _, Y])) Y.


/*
ATOMIC METHODS
*/

atomic constructive_logic existential
     ( seqGoal (H >>> (app exists (tuple [T2, (abs x\ (Prop x))]))))
          true
          true
     ( (existsGoal T2 (Y\ (seqGoal
                 ( (( H >>> (Prop Y))))))))
          notacticyet.

% terminating cases:

atomic constructive_logic trivial
           (seqGoal ( H >>> G )) 
           (memb (hyp G _) H) 
           true 
           trueGoal 
           notacticyet.
atomic constructive_logic trivial
           (seqGoal ( _H >>> trueP)) 
           true
           true
           trueGoal 
           notacticyet.

atomic constructive_logic trivially_false
           (seqGoal ( nil >>> falseP)) 
           true
           true
           falseGoal 
           notacticyet.

atomic constructive_logic false_e 
           (seqGoal ( H >>> _G )) 
           (memb (hyp falseP _) H) 
           true 
           trueGoal
           notacticyet.

atomic constructive_logic false_e 
           (seqGoal ( H >>> _G )) 
           (memb (hyp (app neq (tuple [X, X])) _) H) 
           true 
           trueGoal
           notacticyet.

atomic constructive_logic imp_i 
           (seqGoal (H >>> (app imp (tuple [A, B])))) 
           true
           true 
           (seqGoal ((( (hyp A from_imp)::H) >>> B))) 
           notacticyet.

atomic constructive_logic all_i 
           (seqGoal (H >>> (app forall (tuple [Otype, (abs A)])))) 
           true
           true 
           (allGoal Otype Y\ (seqGoal (((hyp (otype_of Y Otype) nha)::H) >>> (A Y)))) 
           notacticyet.


atomic constructive_logic exists_i 
           (seqGoal (H >>> (app exists (tuple [Otype, (abs A)])))) 
           true
           true 
           (existsGoal Otype Y\ (seqGoal (H >>> (A Y)))) 
           notacticyet.

atomic constructive_logic and_i 
           (seqGoal (H >>> (app and (tuple [A, B])))) 
           true 
           true
           ((seqGoal (H >>> A)) ** (seqGoal (H >>> B))) 
           notacticyet.

atomic constructive_logic and_e 
           (seqGoal (H >>> G )) 
           (memb (hyp (app and (tuple [A, B])) _) H, 
              replace_in_hyps H (hyp (app and (tuple [A, B])) Ann) ((hyp A Ann)::(hyp B Ann)::nil) HH
             )
           true
           (seqGoal (HH >>> G))
           notacticyet.

atomic constructive_logic or_e 
            (seqGoal (H >>> G))
            (memb (hyp (app or (tuple [A, B])) _) H,
             replace_in_hyps H (hyp (app or (tuple [A, B])) A1) ((hyp A A1)::nil) H1,
             replace_in_hyps H (hyp (app or (tuple [A, B])) A2) ((hyp B A2)::nil) H2)
            true
            ((seqGoal (H1 >>> G)) ** (seqGoal (H2 >>> G)))
            notacticyet.

% next, instead of Gentzens rule, use Roy Dyckhoffs versions from
% JSL 1992

atomic constructive_logic  ImpERule
            (seqGoal (H >>> G)) 
            (memb (hyp (app imp (tuple [X, B])) _) H)
            true 
            OutGoal 
            notacticyet:-
         impe_rule ImpERule X B (H >>> G) OutGoal, !.
              %% Warning !! last cut may lose completeness !!

atomic constructive_logic or_il 
	(seqGoal (H >>> (app or (tuple [A, _B])))) 
	true
	true
        (seqGoal (H >>> A)) 
	notacticyet.

atomic constructive_logic or_ir 
	(seqGoal (H >>> (app or (tuple [_A, B])))) 
	true 
	true
        (seqGoal (H >>> B)) 
	notacticyet.

atomic constructive_logic redundant
         (seqGoal (H >>> (app Quant (tuple [_, (abs x\ F)]))))
         (Quant = forall; Quant = exists)
         true  
	 (seqGoal (H >>> F) )
         notacticyet.

atomic constructive_logic redundant
         (seqGoal (H >>> G))
         (memb_and_rest (hyp (otype_of Var T) _) H Rest,
	  not (subterm_of G Var _),
	  not (memb (hyp Hyp _) Rest, subterm_of Hyp Var _))
         true  
	 (seqGoal (Rest >>> G) )
         notacticyet.

atomic constructive_logic neg_i 
	(seqGoal (H >>> (app neg B))) 
	true
        true 
	(seqGoal ((( (hyp  B nha)::H) >>> falseP))) 
	notacticyet.

atomic constructive_logic neg_e 
	(seqGoal ( H >>> falseP )) 
        ((memb (hyp (app neg B) _) H),
          replace_in_hyps H (hyp (app neg B) _) nil H1)
        true
        (seqGoal ( H1 >>> B ))
        notacticyet.

/*  
SUPPORT FOR imp_rule
*/

% recognize atomic formulas

atomic_term(app and (tuple  [_X, _Y] )) :- fail, !.
atomic_term(app or (tuple  [_X,  _Y]) ) :- fail, !.
atomic_term(app imp (tuple [_X, _Y]) ) :- fail, !.
atomic_term(app forall _Y ) :- fail, !.
atomic_term(app exists _Y ) :- fail, !.
atomic_term falseP :- fail, !.      % ! see Dyckhoffs article.
atomic_term( _ ) :- true.             % anything else ....



impe_rule imp_e1 A B (H >>> G) (seqGoal (HH >>> G)) :-
          memb (hyp A _) H,
          atomic_term A,
          replace_in_hyps H (hyp (app imp (tuple [A, B])) Ann) ((hyp B Ann)::nil) HH, !.

impe_rule imp_e2 (app and (tuple [C, D])) B (H >>> G) (seqGoal (HH >>> G)) :-
          replace_in_hyps H (hyp (app imp (tuple [(app and (tuple [C, D])), B]) ) Ann)
                 ((hyp (app imp (tuple [C, (app imp (tuple [D, B]))])) Ann)::nil) HH, !.


impe_rule imp_e3 (app or (tuple [C, D])) B (H >>> G) (seqGoal (HH >>> G) ) :-
          replace_in_hyps H (hyp (app imp (tuple [(app or (tuple [C, D])), B])) Ann)
               ((hyp (app imp (tuple [C, B])) Ann)::(hyp (app imp (tuple [D, B])) Ann)::nil) HH, !.

impe_rule imp_e4 (app imp (tuple [C, D])) B (H >>> G) 
      ((seqGoal (HH >>> G)) ** (seqGoal (HHH >>> (app imp (tuple [C, D]))))) :-
       replace_in_hyps H (hyp (app imp (tuple [(app imp (tuple [C, D])), B])) Ann)
                ((hyp B Ann)::nil) HH, 
      replace_in_hyps H (hyp (app imp (tuple [(app imp (tuple [C, D])), B])) Ann)
                ((hyp (app imp (tuple [D, B])) Ann)::nil) HHH.

% Reintroduce foralls after induction - no backtracking
atomic constructive_logic all_e
        (seqGoal (H >>> G))
        (memb_and_rest (hyp (otype_of X T) _) H NewH, 
	 subterm_of G X _,
	 (not (memb (hyp K An) NewH, subterm_of K X _)), 
         forall_elim X T G NewG,
         (not (subterm_of NewG X _)))
        true
        (seqGoal (NewH >>> NewG))
        notacticyet.

atomic constructive_logic allFi 	
	(seqGoal (H >>> (app forall (tuple [(A arrow B), (abs F)]))))
        true true
        (allGoal (A arrow B) (p\ (seqGoal (H >>> (F p)))))
        notacticyet.


compound constructive_logic taut
      (complete_meth
         (repeat_meth
           (orelse_meth trivial
            (orelse_meth false_e
            (orelse_meth neg_i
            (orelse_meth neg_e
            (orelse_meth imp_i
            (orelse_meth all_i	
            (orelse_meth exists_i 
            (orelse_meth and_i
            (orelse_meth and_e
            (orelse_meth or_e
            (orelse_meth imp_e1
            (orelse_meth imp_e2
            (orelse_meth imp_e3
            (orelse_meth imp_e4
            (orelse_meth or_il or_ir)))))))))))))))))
	_
	true.

%% A couple of easy tautologies

top_goal constructive_logic taut1 [] (app imp (tuple [obj, obj])).
top_goal constructive_logic taut2 [] (app forall (tuple [bool, (abs P\ (app neg (app and (tuple [P, (app neg P)]))))])). 


end
