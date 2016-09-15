% vim: set ft=lprolog:

infixr --> 126. % type arrow
infixl '   255. % infix application
infixl ''  255. % infix System-F application
infixl &&  128. % and
infixl $$  127. % or
infixr ==> 126. % implication
infixr <=> 125. % iff
infix  #in 135. % membership
infix  <<= 130. % subseteq

/* Untrusted predicates called from the kernel:
 * next_object            next object to check
 * callback_proved        proof completed
 * next_tactic            next tactic to use
 * update_certificate     get new certificate after tactic application
 * end_of_proof           is the certificate/proof empty?
 * ppterm                 for pretty-printing messages
 * deftac                 tactic definition
 */

/* Predicates exported from the trusted library:
 * append
 * fold2_append
 * put_binds
 */
 
/* Predicates exported from the kernel:
 * proves
 * check
 */

{ /***** Trusted code base *******/

/***** Trusted library functions *****/

/* The names with ' at the end are trusted; the ones without are
   exported and therefore untrusted. */
local append', fold2_append', put_binds'.

append' [] L L.
append' [ X | XS ] L [ X | RES ] :- append' XS L RES.
append A B C :- append' A B C.

fold2_append' [] [] _ [].
fold2_append' [ X | XS ] [ Y | YS ] F OUTS :-
 F X Y OUT, fold2_append' XS YS F OUTS2, append' OUT OUTS2 OUTS.
fold2_append A B C D :- fold2_append' A B C D.

% put_binds : list 'b -> 'a -> 'c -> list (bounded 'b) -> o
% put_binds [ f1,...,fn ] x t [ bind t x \ f1,...,bind t x fn ]
% binding all the xs that occur in f1,...,fn
put_binds' [] _ _ [].
put_binds' [ YX | YSX ] X A [ bind A Y | YYS ] :-
 YX = Y X, put_binds' YSX X A YYS.
put_binds A B C D :- put_binds' A B C D.

/***** The HOL kernel *****/

local thm, provable, def0, term, typ, typ', loop, prove, check1,
 check1def, check1thm, check1axm, check1nbt,
 reterm, not_defined, check_hyps.

proves T TY :- provable T TY.

typ T :- !. % this line temporarily drops checking of well-formedness for types
            % to avoid too much slow down. It is ultimately due to re-typing
            % terms that should be recognized as already well typed.
typ T :- $is_flex T, !, $delay (typ T) [ T ].
typ T :- typ' T.
typ' prop.
typ' (univ '' A '' B) :- typ A, typ B.
typ' (A --> B) :- typ A, typ B.
typ' (disj_union '' A '' B) :- typ A, typ B.

mode (term i o).
term (lam A F) (A --> B) :- typ A, pi x\ term x A => term (F x) B.
term (F ' T) B :- term F (A --> B), term T A.
term (eq '' A) (A --> A --> prop) :- typ A.
term (?? as T) TY :- $constraint (term T TY) T.

/* like term, but on terms that are already known to be well-typed */
mode (reterm i o).
reterm (lam A F) (A --> B) :- pi x\ reterm x A => reterm (F x) B.
reterm (F ' T) B :- reterm F (A --> B).
reterm (eq '' A) (A --> A --> prop).
reterm (?? as T) TY :- $constraint (reterm T TY) T.

constraint term reterm { /* No propagation rules for now */}

% thm : bounded tactic -> bounded sequent -> list (bounded sequent) -> o
thm C (seq Gamma G) _ :- debug, $print Gamma "|- " G " := " C, fail.

/* << HACKS FOR DEBUGGING */
thm daemon (seq Gamma F) [].
/* >> HACKS FOR DEBUGGING */

thm r (seq Gamma (eq '' _ ' X ' X)) [].
thm (t Y) (seq Gamma (eq '' A ' X ' Z))
 [ seq Gamma (eq '' A ' X ' Y), seq Gamma (eq '' A ' Y ' Z) ] :- term Y A.
thm (m P) (seq Gamma Q) [ seq Gamma (eq '' prop ' P ' Q), seq Gamma P ] :- term P prop.
thm b (seq Gamma (eq '' _ ' ((lam _ F) ' X) ' (F X))) [].
thm c (seq Gamma (eq '' B ' (F ' X) ' (G ' Y)))
 [ seq Gamma (eq '' (A --> B) ' F ' G) , seq Gamma (eq '' A ' X ' Y) ] :- reterm X A, reterm Y A.
thm k (seq Gamma (eq '' (A --> B) ' (lam A S) ' (lam A T)))
 [ bind A x \ seq Gamma (eq '' B ' (S x) ' (T x)) ].
thm s (seq Gamma (eq '' prop ' P ' Q)) [ seq (P :: Gamma) Q, seq (Q :: Gamma) P ].
thm (h IGN) (seq Gamma P) [] :- append' IGN [ P | Gamma2 ] Gamma.

thm d (seq Gamma (eq '' _ ' C ' A)) [] :- def0 C A.
thm (th NAME) (seq _ G) [] :- provable NAME G.

thm (thenll TAC1 TACN) SEQ SEQS :-
 thm TAC1 SEQ NEW,
 deftacl TACN NEW TACL,
 fold2_append' TACL NEW thm SEQS.

/*debprint _ (then _ _) :- !.
debprint _ (thenl _ _) :- !.
debprint O T :- $print O T.*/

thm TAC SEQ SEQS :-
 deftac TAC SEQ XTAC,
 /*debprint "<<" TAC,
 (*/ thm XTAC SEQ SEQS /*, debprint ">>" TAC
 ; debprint "XX" TAC, fail)*/.

thm (! TAC) SEQ SEQS :-
 thm TAC SEQ SEQS,
 !.

thm id SEQ [ SEQ ].

thm (wl Gamma1) (seq Gamma F) [ seq WGamma F ] :-
 append' Gamma1 [ P | Gamma2 ] Gamma,
 append' Gamma1 Gamma2 WGamma.

thm (bind A TAC) (bind A SEQ) NEWL :-
 pi x \ term x A => reterm x A => thm (TAC x) (SEQ x) (NEW x), put_binds' (NEW x) x A NEWL.

thm ww (bind A x \ SEQ) [ SEQ ].

/* debuggin only, remove it */
%thm A B C :- $print "FAILED " (thm A B C), fail.

% loop : list (bounded sequent) -> certificate -> o
%loop SEQS TACS :- $print "LOOP" (loop SEQS TACS), fail.
loop [] CERTIFICATE :- end_of_proof CERTIFICATE.
loop [ SEQ | OLD ] CERTIFICATE :-
 next_tactic [ SEQ | OLD ] CERTIFICATE ITAC,
 thm ITAC SEQ NEW,
 append' NEW OLD SEQS,
 update_certificate CERTIFICATE ITAC NEW NEW_CERTIFICATE,
 loop SEQS NEW_CERTIFICATE.

prove G TACS :-
 (term G prop, ! ; ppterm PG G, $print "Bad statement:" PG, fail),
% (TACS = (false,_), ! ;
 loop [ seq [] G ] TACS
. % ).

not_defined P NAME :-
 not (P NAME _) ; $print "Error:" NAME already defined, fail.

check_hyps HS (typ' TYPE) :-
 (not (typ' TYPE) ; $print "Error:" TYPE already defined, fail), $print HS new TYPE.
check_hyps HS (def0 NAME DEF) :- ppterm PDEF DEF, $print HS NAME "=" PDEF.
check_hyps HS (term NAME TYPE) :-
 not_defined term NAME, ppterm PTYPE TYPE, $print HS NAME ":" PTYPE.
check_hyps HS (reterm _ _).
check_hyps HS (provable NAME TYPE) :-
 not_defined provable NAME, ppterm PTYPE TYPE, $print HS NAME ":" PTYPE.
check_hyps HS (H1,H2) :- check_hyps HS H1, check_hyps HS H2.
check_hyps HS (pi H) :- pi x \ typ' x => check_hyps [x | HS] (H x).
check_hyps HS (_ => H2) :- check_hyps HS H2.

/* check1 I O
   checks the declaration I
   returns the new assumption O */
check1 (theorem NAME GOALTACTICS) HYPS :- check1thm NAME GOALTACTICS HYPS, !.
check1 (axiom NAME ST) HYPS :- check1axm NAME ST HYPS, !.
check1 (new_basic_type TYPE REP ABS REPABS ABSREP PREPH P_TACTICS) HYPS :- check1nbt TYPE REP ABS REPABS ABSREP PREPH P_TACTICS true HYPS, !.
check1 (def NAME TYPDEF) HYPS :- check1def NAME TYPDEF true HYPS, !.
check1 (decl NAME TYP) HYPS :- check1decl NAME TYP true HYPS, !.

check1def NAME (pi I) HYPSUCHTHAT (pi HYPS) :-
 pi x \ typ' x => check1def (NAME '' x) (I x) (HYPSUCHTHAT, typ x) (HYPS x).
check1def NAME (TYP,DEF) HYPSUCHTHAT HYPS :-
 typ TYP, term DEF TYP,
 HYPS = ((HYPSUCHTHAT => term NAME TYP), reterm NAME TYP, def0 NAME DEF).

check1decl NAME (pi I) HYPSUCHTHAT (pi HYPS) :-
 pi x \ typ' x => check1decl (NAME '' x) (I x) (HYPSUCHTHAT, typ x) (HYPS x).
check1decl NAME TYP HYPSUCHTHAT HYPS :-
 typ TYP, HYPS = ((HYPSUCHTHAT => term NAME TYP), reterm NAME TYP).

check1thm NAME (pi I) (pi HYPS) :-
 pi x \ typ' x => check1thm NAME (I x) (HYPS x).
check1thm NAME (GOAL,TACTICS) (provable NAME GOAL) :-
  prove GOAL TACTICS,
  callback_proved NAME GOAL TACTICS.

check1axm NAME (pi I) (pi HYPS) :- !,
 pi x \ typ' x => check1axm NAME (I x) (HYPS x).
check1axm NAME GOAL (provable NAME GOAL) :-
 term GOAL prop, ! ; ppterm PGOAL GOAL, $print "Bad statement:" PGOAL, fail.

check1nbt TYPE REP ABS REPABS ABSREP PREPH (pi P_TACTICS) HYPSUCHTHAT (pi HYPS) :-
 pi x \ typ' x => check1nbt (TYPE '' x) (REP '' x) (ABS '' x) REPABS ABSREP PREPH (P_TACTICS x) (HYPSUCHTHAT, typ x) (HYPS x).
check1nbt TYPE REP ABS REPABS ABSREP PREPH (P,TACTICS) HYPSUCHTHAT HYPS :-
  term P (X --> prop),
  prove (exists '' _ ' P ) TACTICS,
  callback_proved existence_condition (exists '' _ ' P) TACTICS,
  REPTYP = (TYPE --> X),
  ABSTYP = (X --> TYPE),
  ABSREPTYP = (forall '' TYPE ' lam TYPE x \ eq '' TYPE ' (ABS ' (REP ' x)) ' x),
  REPABSTYP = (forall '' X ' lam X x \ impl ' (P ' x) ' (eq '' X ' (REP ' (ABS ' x)) ' x)),
  PREPHTYP = (forall '' TYPE ' lam TYPE x \ (P ' (REP ' x))),
  !,
  HYPS =
   ( (HYPSUCHTHAT => typ' TYPE)
   , (HYPSUCHTHAT => term REP REPTYP), reterm REP REPTYP
   , (HYPSUCHTHAT => term ABS ABSTYP), reterm ABS ABSTYP
   , provable ABSREP ABSREPTYP
   , provable REPABS REPABSTYP, provable PREPH PREPHTYP).

check WHAT :-
 next_object WHAT C CONT,
 (C = stop, !, K = true ; check1 C H , check_hyps [] H, $print_delayed, K = (H => check CONT)),
 !, K.

}

/************ parsing and pretty-printing ********/
% ppterm/parseterm
%ppterm X Y :- ppp X Y. parseterm X Y :- ppp X Y.
%ppp X Y :- $is_flex X, $is_flex Y, !, X = Y.
%ppp X (F ' G) :- $is_flex X, ($is_flex F ; $is_flex G), !, X = (F ' G).
%ppp X (F ' G ' H) :- $is_flex X, ($is_flex F ; $is_flex G ; $is_flex H), !,
% X = (F ' G ' H).

mode (ppp o i) xas ppterm, (ppp i o) xas parseterm.

ppp (! F2) (forall '' _ ' lam _ F1) :- !, pi x \ ppp (F2 x) (F1 x).
ppp (! TY F2) (forall '' TY ' lam TY F1) :- !, pi x \ ppp (F2 x) (F1 x).
ppp (? F2) (exists '' _ ' lam _ F1) :- !, pi x \ ppp (F2 x) (F1 x).
ppp (? TY F2) (exists '' TY ' lam TY F1) :- !, pi x \ ppp (F2 x) (F1 x).
ppp (F2 <=> G2) (eq '' prop ' F1 ' G1) :- !, ppp F2 F1, ppp G2 G1.
ppp (F2 = G2) (eq '' _ ' F1 ' G1) :- !, ppp F2 F1, ppp G2 G1.
ppp (F2 && G2) (and ' F1 ' G1) :- !, ppp F2 F1, ppp G2 G1.
ppp (F2 $$ G2) (or ' F1 ' G1) :- !, ppp F2 F1, ppp G2 G1.
ppp (F2 ==> G2) (impl ' F1 ' G1) :- !, ppp F2 F1, ppp G2 G1.
ppp (X2 #in S2) (in '' _ ' X1 ' S1) :- !, ppp X2 X1, ppp S2 S1.
ppp (U2 <<= V2) (subseteq '' _ ' U1 ' V1) :- !, ppp U2 U1, ppp V2 V1.
ppp (F2 + G2) (plus ' F1 ' G1) :- !, ppp F2 F1, ppp G2 G1.
ppp (F2 ' G2) (F1 ' G1) :- !, ppp F2 F1, ppp G2 G1.
ppp (lam A F2) (lam A F1) :- !, pi x \ ppp (F2 x) (F1 x).
ppp A A.

/* safe_list_map that unifies the two lists if they are both flexible
   probably only useful for parsing/pretty-printing */
safe_list_map L1 _ L2 :- $is_flex L1, $is_flex L2, !, L1 = L2.
safe_list_map L1 F L2 :- list_map L1 F L2.

% pptac(ppterm)/parsetac(parseterm)
% pptac X Y :- ppptac X Y.  parsetac X Y :- ppptac X Y.

mode (ppptac i o) xas parsetac(ppp -> parseterm),
     (ppptac o i) xas pptac(ppp -> ppterm).

ppptac daemon daemon.
ppptac r r.
ppptac (t Y) (t PY) :- ppp Y PY.
ppptac (m Y) (m PY) :- ppp Y PY.
ppptac b b.
ppptac c c.
ppptac k k.
ppptac s s.
ppptac (h Gamma) (h PGamma) :- safe_list_map Gamma ppp PGamma.
ppptac d d.
ppptac (th NAME) (th NAME).
ppptac (thenll TAC1 TACN) (thenll PTAC1 PTACN) :-
 ppptac TAC1 PTAC1, ppptac TACN PTACN.
ppptac (! TAC) (! PTAC) :- ppptac TAC PTAC.
ppptac id id.
ppptac (wl Gamma) (wl PGamma) :- safe_list_map Gamma ppp PGamma.
ppptac (bind A TAC) (bind PA PTAC) :-
 ppp A PA, pi x \ ppptac (TAC x) (PTAC x).
ppptac ww ww.

/************ interactive and non interactive loops ********/

ppptac interactive interactive.

parse_obj (theorem NAME PSTTAC) [theorem NAME STTAC] :-
 parse_thm NAME PSTTAC STTAC.
parse_obj (axiom NAME PTYP) [axiom NAME TYP] :- parse_axiom PTYP TYP.
parse_obj (new_basic_type TYPE REP ABS REPABS ABSREP PREP PP_TACTICS)
 [new_basic_type TYPE REP ABS REPABS ABSREP PREP P_TACTICS] :- parse_nbt PP_TACTICS P_TACTICS.
parse_obj (def NAME PTYBO) [def NAME TYBO] :- parse_def PTYBO TYBO.
parse_obj (decl NAME TY) [decl NAME TY].
parse_obj (inductive_def PRED PREDF PREDF_MON PRED_I PRED_E0 PRED_E K) EXP :-
 inductive_def_pkg PRED PREDF PREDF_MON PRED_I PRED_E0 PRED_E K EXP.
parse_obj stop [stop].

parse_def (pi I) (pi O) :- pi x \ parse_def (I x) (O x).
parse_def (TY,PB) (TY,B) :- parseterm PB B.

parse_axiom (pi I) (pi O) :- !, pi x \ parse_axiom (I x) (O x).
parse_axiom PST ST :- parseterm PST ST.

parse_thm NAME (pi I) (pi O) :- pi x \ parse_thm NAME (I x) (O x).
parse_thm _ (PST,TAC) (ST,(false,TAC)) :- !, parseterm PST ST.
parse_thm NAME PST (ST,(true,[_])) :-
 (not (proves NAME _) ; $print "Error:" NAME already defined, fail),
 parseterm PST ST.

parse_nbt (pi I) (pi O) :- !, pi x \ parse_nbt (I x) (O x).
parse_nbt (PP,TACTICS) (P,(false,TACTICS)) :- parseterm PP P.
parse_nbt PP (P,(true,[_])) :- parseterm PP P.

next_object [ C | NEXT ] CT CONTNEXT :-
  parse_obj C [ CT | CONT ], append CONT NEXT CONTNEXT.
next_object [] C CONT :- 
 $print "Welcome to HOL extra-light",
 toplevel_loop [ C | CONT ].
next_object toplevel C CONT :- toplevel_loop [ C | CONT ].

read_cmd H :-
 $print "Enter a command or \"stop.\"",
 flush std_out, $readterm std_in H,
 !.
read_cmd H :- read_cmd H.

toplevel_loop G :-
 read_cmd H,
 ( H = stop, !, G = [stop]
 ; parse_obj H PH, !, (append PH toplevel G ; $print "error", toplevel_loop G)
 ; $print "bad command", toplevel_loop G ).

callback_proved _ _ (false,_).
callback_proved NAME G (true, [ TAC ]) :-
 canonical TAC CANONICALTAC,
 pptac PCANONICALTAC CANONICALTAC,
 ppterm PG G,
 $print (theorem NAME (PG , [ PCANONICALTAC ] )).

end_of_proof (true, []) :- $print "proof completed".
end_of_proof (false, []).

next_tactic0 [ SEQ | OLD ] (true, [ _ | _ ]) ITAC :-
 $print,
 list_iter_rev [ SEQ | OLD ] print_sequent,
 read_in_context SEQ ITAC BACKTRACK,
 BACKTRACK.
next_tactic0 SEQS (true, CERT) ITAC :-
 $print "error",
 next_tactic SEQS (true, CERT) ITAC.
next_tactic0 SEQS (true_then_false, (_,INT_TACS,_)) ITAC :-
 next_tactic0 SEQS (true, INT_TACS) ITAC.
next_tactic0 SEQS (false, [ interactive | _ ]) ITAC :-
 next_tactic0 SEQS (true, [ _ ]) ITAC.
next_tactic0 [ SEQ | OLD ] (false, [ TAC | _ ]) TAC.
next_tactic0 _ (false, _) ITAC :-
 $print "aborted",
 halt.

next_tactic SEQS CERT TAC :- next_tactic0 SEQS CERT PTAC, parsetac PTAC TAC.

update_certificate (true, [ TAC | OTHER_TACS ]) ITAC NEW (true, TACS) :-
 mk_script ITAC NEW NEW_TACS TAC,
 append NEW_TACS OTHER_TACS TACS.
update_certificate (false, [ interactive | NON_INTERACTIVE_TACS ]) ITAC NEW CERTIFICATE :-
 update_certificate (true_then_false, (SCRIPT, [ SCRIPT ], NON_INTERACTIVE_TACS)) ITAC NEW CERTIFICATE.
update_certificate (true_then_false, (SCRIPT,[ TAC | OTHER_TACS ],NON_INTERACTIVE_TACS)) ITAC NEW CERTIFICATE :- !,
 mk_script ITAC NEW NEW_INTERACTIVE_TACS TAC,
 append NEW_INTERACTIVE_TACS OTHER_TACS INTERACTIVE_TACS,
 ( INTERACTIVE_TACS = [ _ | _ ], !,
   CERTIFICATE =
    (true_then_false, (SCRIPT,INTERACTIVE_TACS,NON_INTERACTIVE_TACS))
 ; CERTIFICATE = (false, NON_INTERACTIVE_TACS),
   $print "INTERACTIVE SUBPROOF COMPLETED",
   canonical SCRIPT CSCRIPT,
   pptac PSCRIPT CSCRIPT,
   $print PSCRIPT).
update_certificate (false, [ _ | OTHER_TACS ]) _ _ (false, OTHER_TACS).

mk_script (bind A T) NEW NEW_TACS (bind A T2) :- !,
 pi x \
  put_binds (NEW2 x) x A NEW,
  mk_script (T x) (NEW2 x) (NEWT x) (T2 x),
  put_binds (NEWT x) x A NEW_TACS.
mk_script ITAC NEW NEW_TACS (thenl ITAC NEW_TACS) :-
 mk_list_of_bounded_fresh NEW NEW_TACS.

read_in_context (bind A K) (bind A TAC) BACKTRACK :-
 pi x \ /* term x A => reterm ' x A => */ read_in_context (K x) (TAC x) BACKTRACK.
read_in_context (seq A B) TAC BACKTRACK :-
 flush std_out, $readterm std_in TAC,
 (TAC = backtrack, !, BACKTRACK = (!, fail) ; BACKTRACK = true).

print_sequent (seq Gamma G) :-
 $print,
 list_iter_rev Gamma (x \ sigma PX \ ppterm PX x, $print PX),
 $print "|------------------",
 ppterm PG G, $print PG.
print_sequent (bind A F) :- pi x \ print_sequent (F x).

/* turns thenl into then */
canonical (bind A T1) (bind A T2) :- !,
 pi x \ canonical (T1 x) (T2 x).
canonical (thenl T L) OTAC :- !,
 list_map L canonical L2,
 (mk_constant_list L2 S L2, !,
  (S = [], !, OTAC = T ; OTAC = then T S)
 ; OTAC = thenl T L2).
canonical T T.

/************ inductive_def package ********/
parse_inductive_def_spec (pi F) (pi PF) :- !,
 pi A \ parse_inductive_def_spec (F A) (PF A).
parse_inductive_def_spec (param TY F) (param PTY PF) :- !,
 ppp TY PTY, pi x \ parse_inductive_def_spec (F x) (PF x).
parse_inductive_def_spec L PL :-
 (pi p \ list_map (L p)
  (x \ px \ sigma A \ sigma B \ sigma PB \ x = (A, B), parseterm B PB, px = (A, PB))
  (PL p)).

build_quantified_predicate (pi I) (pi O) :- !,
 pi A \ build_quantified_predicate (I A) (O A).
build_quantified_predicate (param TY I) (TY --> TYP, lam TY BO) :- !,
 pi x \ build_quantified_predicate (I x) (TYP, BO x).
build_quantified_predicate L (_, lam _ p \ lam _ x \ P p x) :-
 pi p \ pi x \ build_predicate (L p) p x (P p x).

build_predicate [ (_,K) ] P X R :- !,
 process_constructor K P X R.
build_predicate [ (_,K) | REST ] P X (or ' Q ' R) :-
 process_constructor K P X Q,
 build_predicate REST P X R.

process_constructor (forall '' TY ' lam TY Q) P X (exists '' TY ' lam TY R) :-
 pi y \ process_constructor (Q y) P X (R y).
process_constructor (impl ' H ' K) P X (and ' H ' R) :-
 process_constructor K P X R.
process_constructor (P ' T) P X (eq '' _ ' X ' T).

prove_monotonicity_thm (pi F) PREDF APREDF (pi THM) :- !,
 pi A \ prove_monotonicity_thm (F A) PREDF (APREDF '' A) (THM A).
prove_monotonicity_thm (param TY F) PREDF APREDF (forall '' TY ' lam TY STM, PROOF) :- !,
 pi x \ prove_monotonicity_thm (F x) PREDF (APREDF ' x) (STM x, PROOF).
prove_monotonicity_thm _ PREDF APREDF THM :-
 THM =
  (monotone '' _ ' APREDF,
   [ then inv (bind* (then (conv (depth_tac (dd [PREDF]))) auto_monotone)) ]).

state_fixpoint_def (pi F) PREDF (pi DEF) :- !,
 pi A \ state_fixpoint_def (F A) (PREDF '' A) (DEF A).
state_fixpoint_def (param TY F) PREDF (_, lam TY BO) :- !,
 pi x \ state_fixpoint_def (F x) (PREDF ' x) (_, BO x).
state_fixpoint_def _ PREDF (_, fixpoint '' _ ' PREDF).

prove_fix_intro_thm (pi F) PREDF PRED PREDF_MONOTONE (pi THM) :- !,
 pi A \ prove_fix_intro_thm (F A) (PREDF '' A) (PRED '' A) PREDF_MONOTONE (THM A).
prove_fix_intro_thm (param TY F) PREDF PRED PREDF_MONOTONE (forall '' TY ' lam TY STM, [ then forall_i (bind _ PROOF) ]) :- !,
 pi x \ prove_fix_intro_thm (F x) (PREDF ' x) (PRED ' x) PREDF_MONOTONE (STM x, [ PROOF x ]).
prove_fix_intro_thm _ PREDF PRED PREDF_MONOTONE THM :-
 THM =
  ((! x \ PREDF ' PRED ' x ==> PRED ' x),
   [then forall_i
     (bind _ x13 \
       then (conv (rand_tac (rator_tac dd)))
        (then (conv (land_tac (rator_tac (rand_tac dd))))
          (then inv
            (then (cutth fixpoint_is_prefixpoint)
              (then (lforall PREDF)
                (thenl lapply [applyth PREDF_MONOTONE,
                  then
                   (g
                     (subseteq '' _ '
                       (PREDF ' (fixpoint '' _ ' PREDF)) '
                       (fixpoint '' _ ' PREDF)))
                   (then (conv (depth_tac (dd [subseteq])))
                     (then (conv (depth_tac (dd [in])))
                       (then (conv (depth_tac (dd [in])))(itaut 4))))]))))))]).

prove_fix_elim_thm (pi F) PREDF PRED OPRED (pi THM) :- !,
 pi A \ prove_fix_elim_thm (F A) (PREDF '' A) (PRED '' A) OPRED (THM A).
prove_fix_elim_thm (param TY F) PREDF PRED OPRED (forall '' TY ' lam TY STM, [ then forall_i (bind _ PROOF) ]) :- !,
 pi x \ prove_fix_elim_thm (F x) (PREDF ' x) (PRED ' x) OPRED (STM x, [ PROOF x ]).
prove_fix_elim_thm _ PREDF PRED OPRED THM :-
 THM =
  ((! x13 \
     (! x14 \ PREDF ' x13 ' x14 ==> x13 ' x14) ==>
      (! x14 \ PRED ' x14 ==> x13 ' x14)) ,
    [then forall_i
      (bind _ x23 \
        then (cutth fixpoint_subseteq_any_prefixpoint)
         (then (lforall PREDF)
           (then (lforall x23)
             (then (conv (depth_tac (dd [OPRED])))
               (then inv
                 (bind _ x24 \
                   then
                    (g
                      (impl ' (subseteq '' _ ' (PREDF ' x23) ' x23) '
                        (subseteq '' _ ' (fixpoint '' _ ' PREDF) ' x23)))
                    (then (conv (depth_tac (dd [subseteq])))
                      (then (conv (depth_tac (dd [subseteq])))
                        (then (conv (depth_tac (dd [in])))
                          (then (conv (depth_tac (dd [in])))
                            (then (conv (depth_tac (dd [in])))
                              (then (conv (depth_tac (dd [in])))
                                (then
                                  (w
                                    (impl '
                                      (subseteq '' _ ' (PREDF ' x23) ' x23) '
                                      (subseteq '' _ '
                                        (fixpoint '' _ ' PREDF) ' x23)))
                                  (then inv
                                    (thenl lapply_last [h,
                                      then (lforall_last x24)
                                       (then lapply_last h)])))))))))))))))]).

prove_intro_thms (pi F) PRED PRED_I INTROTHMS :- !,
 pi A \
  prove_intro_thms (F A) (PRED '' A) PRED_I (OUT A),
  list_map (OUT A)
   (i \ o \ sigma Y \ i = (theorem NAME (P A)), o = theorem NAME (pi P))
   INTROTHMS.
prove_intro_thms (param TY F) PRED PRED_I INTROTHMS :- !,
 pi x \
  prove_intro_thms (F x) (PRED ' x) PRED_I (OUT x),
  list_map (OUT x)
   (i \ o \ sigma Y \
     i = (theorem NAME (STM x, [ PROOF x ])),
     o = theorem NAME (forall '' TY ' lam TY STM, [ then forall_i (bind TY PROOF) ]))
   INTROTHMS.
prove_intro_thms L PRED PRED_I INTROTHMS :-
 list_map (L PRED) (mk_intro_thm PRED_I) INTROTHMS.

mk_intro_thm PRED_I (NAME,ST)
 (theorem NAME (ST,
   [ daemon /*(then inv (bind* (then (applyth PRED_I) (then (conv dd) (itauteq 6)))))*/ /* TOO MANY GOALS DELAYED ON typ (???): USE daemon INSTEAD */ ])).

inductive_def_pkg PRED PREDF PREDF_MONOTONE PRED_I PRED_E0 PRED_E L OUT :-
 parse_inductive_def_spec L PL,
 build_quantified_predicate PL F,
 prove_monotonicity_thm PL PREDF PREDF MONTHM,
 state_fixpoint_def PL PREDF FIXDEF,
 prove_fix_intro_thm PL PREDF PRED PREDF_MONOTONE INTROTHM,
 prove_intro_thms PL PRED PRED_I INTROTHMS,
 prove_fix_elim_thm PL PREDF PRED PRED ELIMTHM,
 OUT1 =
  [ def PREDF F
  , theorem PREDF_MONOTONE MONTHM
  , def PRED FIXDEF
  , theorem PRED_I INTROTHM
  , theorem PRED_E0 ELIMTHM ],
 append OUT1 INTROTHMS OUT.

/************ library of basic data types ********/
mk_bounded_fresh (bind _ F) (bind _ G) :- !, pi x\ mk_bounded_fresh (F x) (G x).
mk_bounded_fresh _ X.

mk_list_of_bounded_fresh [] [].
mk_list_of_bounded_fresh [S|L] [X|R] :-
 mk_bounded_fresh S X, mk_list_of_bounded_fresh L R.

/* list functions */

list_map [] _ [].
list_map [X|XS] F [Y|YS] :- F X Y, list_map XS F YS.

list_iter_rev [] _.
list_iter_rev [X|XS] F :- list_iter_rev XS F, F X.

mem [ X | _ ] X, !.
mem [ _ | XS ] X :- mem XS X.

mk_constant_list [] _ [].
mk_constant_list [_|L] X [X|R] :- mk_constant_list L X R.

bang P :- P, !.

/********** tacticals ********/

% BUG in runtime.ml if the sigma is uncommented out. It does not matter btw.
/*sigma ff \*/ deftac fail SEQ ff.

ppptac (constant_tacl TACL) (constant_tacl PTACL) :-
 list_map TACL ppptac PTACL.
deftacl (constant_tacl TACL) SEQS TACL.

ppptac (thenl TAC TACL) (thenl PTAC PTACL) :-
 ppptac TAC PTAC, list_map TACL ppptac PTACL. 
deftac (thenl TAC TACL) SEQ XTAC :-
 XTAC = thenll TAC (constant_tacl TACL).

ppptac (all_equals_list TAC) (all_equals_list PTAC) :- ppptac TAC PTAC.
deftacl (all_equals_list TAC2) SEQS TACL :-
 mk_constant_list SEQS TAC2 TACL.

ppptac (then TAC1 TAC2) (then PTAC1 PTAC2) :-
 ppptac TAC1 PTAC1, ppptac TAC2 PTAC2.
deftac (then TAC1 TAC2) SEQ XTAC :-
 XTAC = thenll TAC1 (all_equals_list TAC2).

ppptac (then! TAC1 TAC2) (then! PTAC1 PTAC2) :-
 ppptac TAC1 PTAC1, ppptac TAC2 PTAC2.
deftac (then! TAC1 TAC2) _ (then (! TAC1) TAC2).

ppptac (orelse TAC1 TAC2) (orelse PTAC1 PTAC2) :-
 ppptac TAC1 PTAC1, ppptac TAC2 PTAC2.
deftac (orelse TAC1 TAC2) SEQ XTAC :-
 XTAC = TAC1 ; XTAC = TAC2.

ppptac (orelse! TAC1 TAC2) (orelse! PTAC1 PTAC2) :-
 ppptac TAC1 PTAC1, ppptac TAC2 PTAC2.
deftac (orelse! TAC1 TAC2) _ (orelse (! TAC1) TAC2).

ppptac (bind* TAC) (bind* PTAC) :- ppptac TAC PTAC.
deftac (bind* TAC) SEQ (orelse! (bind _ x \ bind* TAC) TAC).

ppptac (repeat TAC) (repeat PTAC) :- ppptac TAC PTAC.
deftac (repeat TAC) SEQ XTAC :-
 ( XTAC = then TAC (repeat (bind* TAC))
 ; XTAC = id).

ppptac (repeat! TAC) (repeat! PTAC) :- ppptac TAC PTAC.
deftac (repeat! TAC) SEQ (orelse! (then! TAC (repeat! (bind* TAC))) id).

ppptac (pptac TAC) (pptac PTAC) :- ppptac TAC PTAC.
deftac (pptac TAC) SEQ TAC :-
 $print "SEQ" SEQ ":=" TAC.

ppptac (time TAC) (time PTAC) :- ppptac TAC PTAC.
deftac (time TAC) SEQ XTAC :-
 $gettimeofday B,
 XTAC = thenll TAC (time_after TAC B).

ppptac (time_after TAC B) (time_after PTAC B) :- ppptac TAC PTAC.
deftacl (time_after TAC B) SEQS TACL :-
 $gettimeofday A,
 D is A - B,
 mk_constant_list SEQS id TACL,
 $print "TIME SPENT " D "FOR" TAC.

/* For debugging only (?) For capturing metavariables */
ppptac (inspect (seq Gamma F) TAC) (inspect (seq PGamma PF) PTAC) :-
 list_map SEQ ppp PSEQ, ppp F PF, ppptac TAC PTAC.
deftac (inspect SEQ TAC) SEQ TAC.

/********** tactics ********/

ppptac (w G) (w PG) :- ppp G PG.
deftac (w G) (seq Gamma _) (wl Gamma1) :-
 append Gamma1 [ G | _ ] Gamma.

ppptac h h.
deftac h SEQ (h L).

/*** eq ***/

ppptac sym sym.
deftac sym (seq Gamma (eq '' T ' L ' R)) TAC :-
 TAC = thenl (m (eq '' T ' R ' R)) [ thenl c [ thenl c [ r , id ] , r ] , r ].

ppptac eq_true_intro eq_true_intro.
deftac eq_true_intro (seq Gamma (eq '' prop ' P ' tt)) TAC :-
 TAC = thenl s [ th tt_intro, wl [] ].

/*** true ***/

/*** and ***/

ppptac conj conj.
deftac conj (seq Gamma (and ' P ' Q)) TAC :-
 TAC =
  then
   (then (conv dd)
     (then k (bind _ x \
       thenl c
        [ thenl c [ r, eq_true_intro ] ,
          eq_true_intro ])))
   ww.

/* Gamma  "|-"  q    --->   Gamma "|-" and ' p ' q*/
ppptac (andr P) (andr PP) :- ppp P PP.
deftac (andr P) (seq Gamma Q) TAC :-
 TAC =
  (thenl (m ((lam _ f \ f ' P ' Q) ' (lam _ x \ lam _ y \ y)))
    [ then
       %(repeat (conv (depth_tac b))) ROBUS VERSION LINE BELOW
       (then (conv (land_tac b)) (then (conv (land_tac (rator_tac b))) (conv (land_tac b))))
      r
    , thenl (conv (rator_tac id))
       [ then (thenl (t (lam _ f \ f ' tt ' tt)) [ id, r ])
          (thenl (m (and ' P ' Q)) [ dd , id ])
       , then (repeat (conv (depth_tac b))) (th tt_intro) ]]).

/* (and ' p ' q) :: nil  "|-"  q */
ppptac andr andr.
deftac andr (seq Gamma Q) TAC :-
 mem Gamma (and ' P ' Q),
 TAC = then (andr P) h.

/* Gamma  "|-"  p    --->   Gamma "|-" and ' p ' q*/
ppptac (andl P) (andl PP) :- ppp P PP.
deftac (andl Q) (seq Gamma P) TAC :-
 TAC =
  (thenl (m ((lam _ f \ f ' P ' Q) ' (lam _ x \ lam _ y \ x)))
    [ then
       %(repeat (conv (depth_tac b))) ROBUS VERSION LINE BELOW
       (then (conv (land_tac b)) (then (conv (land_tac (rator_tac b))) (conv (land_tac b))))
      r
    , thenl (conv (rator_tac id))
       [ then (thenl (t (lam _ f \ f ' tt ' tt)) [ id, r ])
          (thenl (m (and ' P ' Q)) [ dd , id ])
       , then (repeat (conv (depth_tac b))) (th tt_intro) ]]).

/* (and ' p ' q) :: nil  "|-"  p */
ppptac andl andl.
deftac andl (seq Gamma P) TAC :-
 mem Gamma (and ' P ' Q),
 TAC = then (andl Q) h.


/*** forall ***/

/* |- forall ' F  -->   |- F ' x */
ppptac forall_i forall_i.
deftac forall_i (seq Gamma (forall '' _ ' lam _ G)) TAC :-
 TAC = then (conv dd) (then k (bind _ x \ eq_true_intro)).

/* forall ' F |- F ' T */
ppptac forall_e forall_e.
deftac forall_e (seq Gamma GX) TAC :-
 mem Gamma (forall '' _ ' (lam _ G)), GX = G X,
 TAC = thenl (m ((lam _ G) ' X)) [ b, thenl (m ((lam _ z \ tt) ' X))
  [ thenl c [ then sym (thenl (m (forall '' _ ' lam _ G)) [dd,h ]), r ]
  , then (conv b) (th tt_intro) ] ].

/* forall ' F |- f  -->  F ' a, forall ' F |- f */
ppptac (lforall F A) (lforall PF PA) :- ppp F PF, ppp A PA.
deftac (lforall F A) (seq Gamma G) TAC :-
 TAC = thenl (m (impl ' (F A) ' G))
  [ thenl s [ then mp forall_e, then i h ] , then (w (forall '' _ ' lam _ F)) i ].

/* forall ' F |- f  -->  F ' a, forall ' F |- f */
ppptac (lforall A) (lforall PA) :- ppp A PA.
deftac (lforall A) (seq Gamma G) (lforall F A) :-
 mem Gamma (forall '' _ ' lam _ F).

/* forall ' F |- f  -->  F ' a, forall ' F |- f */
ppptac lforall lforall.
deftac lforall (seq Gamma G) (lforall A).

/* forall ' F |- f  -->  F ' a, forall ' F |- f */
ppptac (lforall_last A) (lforall_last PA) :- ppp A PA.
deftac (lforall_last A) (seq ((forall '' _ ' lam _ F)::Gamma) G) (lforall F A).

/*** false ***/
              
/*** impl ***/

/* |- p=>q  -->  p |- q */
ppptac i i.
deftac i (seq Gamma (impl ' P ' Q)) TAC :-
 TAC = then (conv dd) (thenl s [ andl, thenl conj [ h [], id ]]).

/* p=>q |- q  -->  |- p */
ppptac (mp P) (mp PP) :- ppp P PP.
deftac (mp P) (seq Gamma Q) TAC :-
 TAC = then (andr P) (thenl (m P) [ then sym (thenl (m (impl ' P ' Q)) [ dd , h ]) , id ]).

/* p=>q |- q  -->  |- p */
ppptac mp mp.
deftac mp (seq Gamma Q) (mp P) :-
 mem Gamma (impl ' P ' Q).

/* |- q   -->   p |- q  and  |- p */
ppptac (cut P) (cut PP) :- ppp P PP.
deftac (cut P) (seq Gamma Q) TAC :-
 TAC = then (andr P) (thenl (m P) [then sym (thenl (m (impl ' P ' Q)) [then (conv (land_tac dd)) r, i] ) , id]). 

/* |-q  --> p |- q   where the theorem T proves p */
ppptac (cutth P) (cutth PP) :- ppp P PP.
deftac (cutth T) SEQ TAC :-
 proves T X,
 TAC = (thenl (cut X) [ id, th T ]).

/* applies the theorem T */
ppptac (applyth P) (applyth PP) :- ppp P PP.
deftac (applyth T) SEQ (then (cutth T) apply_last).

/* impl p q, Gamma |- f   --->   /*impl q f*/ Gamma |- p  ,  q, Gamma |- f */
ppptac (lapply P Q) (lapply PP PQ) :- ppp P PP, ppp Q PQ.
deftac (lapply P Q) (seq Gamma F) TAC :-
 TAC =
  thenl (m (impl ' Q ' F)) [ thenl s [ then (mp Q) (then (w (impl ' Q ' F)) (then (mp P) (w (impl ' P ' Q)))) , then i (h [A]) ] , then (w (impl ' P ' Q)) (then i id) ].

/* impl p q, Gamma |- f   --->   /*impl q f*/ Gamma |- p  ,  q, Gamma |- f */
ppptac lapply lapply.
deftac lapply (seq Gamma F) (lapply P Q) :-
 mem Gamma (impl ' P ' Q).

/* impl p q, Gamma |- f   --->   /*impl q f*/ Gamma |- p  ,  q, Gamma |- f */
ppptac lapply_last lapply_last.
deftac lapply_last (seq ((impl ' P ' Q)::Gamma) F) (lapply P Q).

/* p |- f ---> p |- p ==> f */
ppptac (g P) (g PP) :- ppp P PP.
deftac (g P) (seq _ F) TAC :-
 TAC =
  (thenl (m (impl ' P ' F)) [thenl s [then mp h , then i h] , id ]).

/*** not ***/

/*** exists ***/

/**** apply, i.e. forall + impl ****/

ppptac (apply X) (apply PX) :- ppp X PX.
deftac (apply X) SEQ h :- $is_flex X, !.
deftac (apply X) SEQ h.
deftac (apply (impl ' P ' Q)) SEQ TAC :-
 TAC = thenl (lapply P Q) [ id, apply_last ].
deftac (apply (forall '' _ ' lam _ G)) SEQ TAC :-
 TAC = then (lforall G X) apply_last.

ppptac apply_last apply_last.
deftac apply_last (seq (H::Gamma) F) (apply H).

ppptac apply apply.
deftac apply (seq Gamma F) (apply H) :-
 mem Gamma H.

/********** conversion(als) ***********/

strip_constant (I '' _) H :- !, strip_constant I H.
strip_constant H H.

/* expands definitions, even if applied to arguments */
ppptac (dd L) (dd L).
deftac (dd L) (seq _ (eq '' _ ' T ' X)) d :- strip_constant T H, bang (mem L H).
deftac (dd L) (seq _ (eq '' _ ' (D ' T) ' X))
 (thenl (t A) [thenl c [dd L , r], b]).

ppptac dd dd.
deftac dd _ (dd L).

ppptac beta_expand beta_expand.
deftac beta_expand (seq _ (eq '' _ ' (lam _ x \ F x) ' (lam _ x \ (lam _ F) ' x))) TAC :-
 TAC = then k (bind _ x \ then sym b).

/* folds a definition, even if applied to arguments */
/* BUG: it seems to fail with restriction errors in some cases */
ppptac f f.
deftac f SEQ (then sym dd).

ppptac (rand_tac C) (rand_tac PC) :- ppptac C PC.
deftac (rand_tac C) SEQ TAC :-
  TAC = thenl c [ r , C ].

ppptac (rator_tac C) (rator_tac PC) :- ppptac C PC.
deftac (rator_tac C) SEQ TAC :-
  TAC = thenl c [ C , r ].

ppptac (abs_tac C) (abs_tac PC) :- ppptac C PC.
deftac (abs_tac C) SEQ TAC :-
  TAC = then k (bind A x \ C).

ppptac (land_tac C) (land_tac PC) :- ppptac C PC.
deftac (land_tac C) SEQ TAC :-
  TAC = thenl c [ thenl c [ r, C ] , r ].

ppptac (sub_tac C) (sub_tac PC) :- ppptac C PC.
deftac (sub_tac C) SEQ TAC :-
  TAC = orelse (rand_tac C) (orelse (rator_tac C) (abs_tac C)).

ppptac (try TAC) (try PTAC) :- ppptac TAC PTAC.
deftac (try TAC) SEQ (orelse TAC id).

ppptac (depth_tac C) (depth_tac PC) :- ppptac C PC.
deftac (depth_tac C) SEQ TAC :-
  TAC = then (try C) (sub_tac (depth_tac C)).

ppptac (conv C) (conv PC) :- ppptac C PC.
deftac (conv C) (seq Gamma F) TAC :-
 TAC = thenl (m G) [ then sym C , id ].

/********** Automation ***********/
/* TODO:
 1) our lforall gets rid of the hypothesis (bad) */
/* left tries to reduce the search space via focusing */
ppptac left left.
deftac left (seq Gamma _) TAC :-
 mem Gamma (not ' F),
 TAC =
  (!
   (then (cutth not_e)
    (then (lforall_last F)
     (thenl lapply [ h, (w (not ' F)) ])))).
deftac left (seq Gamma _) TAC :-
 /* A bit long because we want to beta-reduce the produced hypothesis.
    Maybe this should be automatized somewhere else. */
 mem Gamma (exists '' _ ' F),
 TAC =
  (!
   (then (cutth exists_e)
    (then (lforall_last F)
     (thenl lapply [ h, then (w (exists '' _ ' F)) (then apply_last (then forall_i (bind _ x \ then (try (conv (land_tac b))) i))) ])))).
deftac left (seq Gamma H) TAC :-
 mem Gamma (or ' F ' G),
 TAC =
  (!
   (then (cutth or_e)
    (then (lforall_last F)
     (then (lforall_last G)
      (then (lforall_last H)
       (thenl lapply [ h, then (w (or ' F ' G)) (then apply_last i)])))))).
deftac left (seq Gamma H) TAC :-
 mem Gamma (and ' F ' G),
 TAC =
  (!
   (then (cutth and_e)
    (then (lforall_last F)
     (then (lforall_last G)
      (then (lforall_last H)
       (thenl lapply [ h, then (w (and ' F ' G)) (then apply_last (then i i))])))))).
deftac left (seq Gamma H) TAC :-
 mem Gamma (eq '' TY ' F ' G),
 not ($is_flex TY), TY = prop,
 TAC =
  (then (g (eq '' TY ' F ' G))
   (then (conv (land_tac (then (applyth eq_to_impl) h)))
     (then i (w (eq '' TY ' F ' G))))).

ppptac not_i not_i.
deftac not_i (seq _ (not ' _)) (applyth not_i).

ppptac inv inv.
deftac inv _ TAC :-
 TAC =
 (then!
  (repeat!
   (orelse! conj (orelse! forall_i (orelse! i (orelse! not_i s)))))
  (bind* (repeat! left))).

ppptac (sync N) (sync N).
deftac (sync N) (seq _ tt) (th tt_intro).
deftac (sync N) (seq Gamma _) (then (applyth ff_elim) h) :-
 mem Gamma ff.
deftac (sync N) (seq _ (or ' _ ' _))
 (orelse (then (applyth orr) (itaut N)) (then (applyth orl) (itaut N))).
deftac (sync N) (seq _ (exists '' _ ' _)) (then (applyth exists_i) (then (conv b) (itaut N2))) :-
 N2 is N - 2.

ppptac (itaut N) (itaut N).
deftac (itaut N) SEQ fail :- N =< 0, !.
deftac (itaut N) SEQ TAC :-
 %$print (itaut N) SEQ,
 N1 is N - 1,
 N2 is N - 2,
 TAC =
 (then! inv
  (bind*
   (orelse h
   (orelse (sync N)
   (orelse /* Hypothesis not moved to front */ (then lforall (itaut N2))
   (then lapply (itaut N1))))))).

ppptac (itauteq N) (itauteq N).
deftac (itauteq N) _ (then (cutth eq_reflexive) (itaut N)).

/********** inductive predicates package ********/

ppptac monotone monotone.
deftac monotone (seq _ (impl ' X ' X)) (! (then i h)) :- !.
deftac monotone (seq [forall '' _ ' lam _ x \ impl ' (F ' x) ' (G ' x)] (impl ' (F ' T) ' (G ' T))) (! apply) :- !.
deftac monotone (seq _ (impl ' (and ' _ ' _) ' _)) TAC :-
 TAC = then (applyth and_monotone) monotone.
deftac monotone (seq _ (impl ' (or ' _ ' _) ' _)) TAC :-
 TAC = then (applyth or_monotone) monotone.
deftac monotone (seq _ (impl ' (impl ' _ ' _) ' _)) TAC :-
 TAC = then (applyth impl_monotone) monotone.
deftac monotone (seq _ (impl ' (not ' _) ' _)) TAC :-
 TAC = then (applyth not_monotone) monotone.
deftac monotone (seq _ (impl ' (forall '' _ ' lam _ _) ' _)) TAC :-
 TAC =
  then (conv (land_tac (rand_tac beta_expand)))
   (then (conv (rand_tac (rand_tac beta_expand)))
     (then (applyth forall_monotone) (then forall_i (bind _ x \
       then (conv (depth_tac b)) (then (conv (depth_tac b)) monotone))))).
deftac monotone (seq _ (impl ' (exists '' _ ' lam _ _) ' _)) TAC :-
 TAC =
  then (conv (land_tac (rand_tac beta_expand)))
   (then (conv (rand_tac (rand_tac beta_expand)))
     (then (applyth exists_monotone) (then forall_i (bind _ x \
       then (conv (depth_tac b)) (then (conv (depth_tac b)) monotone))))).

/* expands "monotone ' (lam _ f \ lam _ x \ X f x)" into
   "! x \ p ' x ==> q ' x |- X p y ==> X q y"
   and then calls the monotone tactic */
ppptac auto_monotone auto_monotone.
deftac auto_monotone _ TAC :-
 TAC =
  then (conv dd)
   (then forall_i (bind _ p \ (then forall_i (bind _ q \
     then (conv (land_tac dd))
      (then (conv (land_tac (depth_tac (dd [in]))))
        (then (conv (land_tac (depth_tac (dd [in]))))
          (then i
            (then (conv dd)
              (then forall_i (bind _ x \
                (then (conv (land_tac dd))
                  (then (conv (rand_tac dd))
                    (then (conv (land_tac (rator_tac b)))
                      (then (conv (land_tac b))
                        (then (conv (rand_tac (rator_tac b)))
                          (then (conv (rand_tac b))
                            monotone)))))))))))))))).

/********** the library ********/

main :- the_library L, append L [stop] Lstop, check Lstop.

go :- the_library L, check L.

the_library L :-
 L =
  [ /******** Primivite operators hard-coded in the kernel ******/
  % decl eq (pi A \ A --> A --> prop)

  /********** Axiomatization of choice over types ********/
    decl choose (pi A \ A)

  /*********** Connectives and quantifiers ********/
  , def tt (prop,((lam prop x \ x) = (lam prop x \ x)))
  , def forall (pi A \ ((A --> prop) --> prop),
     (lam (A --> prop) f \ f = (lam A g \ tt)))
  , def ff (prop,(! x \ x))
  , def and ((prop --> prop --> prop),
     (lam _ x \ lam _ y \ (lam (prop --> prop --> prop) f \ f ' x ' y) = (lam _ f \ f ' tt ' tt)))
  , def impl ((prop --> prop --> prop),(lam _ a \ lam _ b \ a && b <=> a))
  , def exists (pi A \ ((A --> prop) --> prop),
     (lam (A --> prop) f \ ! c \ (! a \ f ' a ==> c) ==> c))
  , def not ((prop --> prop),(lam _ x \ x ==> ff))
  , def or ((prop --> prop --> prop),
     (lam _ x \ lam _ y \ ! c \ (x ==> c) ==> (y ==> c) ==> c))
  , theorem tt_intro (tt,[then (conv dd) (then k (bind _ x12 \ r))])
  , theorem ff_elim ((! p \ ff ==> p),
    [then forall_i (bind prop x3\ then (conv (land_tac dd)) (then i forall_e))])
  , theorem sym ((! p \ ! q \ p = q ==> q = p),
    [then forall_i
     (bind prop x12 \
       then forall_i
        (bind prop x13 \
          then i (then sym h)))])
  , theorem not_e ((! p \ not ' p ==> p ==> ff),
     [then forall_i (bind prop x3 \ then (conv (land_tac dd)) (then i h))])
  , theorem conj ((! p \ ! q \ p ==> q ==> p && q),
    [then forall_i
     (bind prop x12 \
      then forall_i (bind prop x13 \ then i (then i (then conj h))))])
  , theorem andl ((! p \ ! q \ p && q ==> p),
    [then forall_i
     (bind prop x12 \
      then forall_i (bind prop x13 \ then i (then (andl x13) h)))])
  , theorem andr ((! p \ ! q \ p && q ==> q),
    [then forall_i
     (bind prop x12 \
      then forall_i (bind prop x13 \ then i (then (andr x12) h)))])
  , theorem and_e ((! p \ ! q \ ! c \ p && q ==> (p ==> q ==> c) ==> c),
     [then forall_i
       (bind prop x12 \
         then forall_i
          (bind prop x13 \
            then forall_i
             (bind prop x14 \ then i (then i (thenl apply [andl, andr])))))])
  , theorem not_i ((! p \ (p ==> ff) ==> not ' p),
     [then forall_i (bind prop x2 \ then i (then (conv dd) h))])
  , theorem orl ((! p \ ! q \ p ==> p $$ q),
      [then forall_i
        (bind prop x12 \
          then forall_i
           (bind prop x13 \
             then i
              (then (conv dd)
                (then forall_i (bind prop x14 \ then i (then i (then apply h)))))))])
  , theorem orr ((! p \ ! q \ q ==> p $$ q),
      [then forall_i
        (bind prop x12 \
          then forall_i
           (bind prop x13 \
             then i
              (then (conv dd)
                (then forall_i (bind prop x14 \ then i (then i (then apply h)))))))])
  , theorem or_e ((! p \ ! q \ ! c \ p $$ q ==> (p ==> c) ==> (q ==> c) ==> c),
     [then forall_i
       (bind prop x12 \
         then forall_i
          (bind prop x13 \
            then forall_i
             (bind prop x14 \ then (conv (land_tac dd)) (then i forall_e))))])
  , theorem exists_e (pi T \
     (! f \ (exists '' T ' f) ==> (! c \ (! x \ f ' x ==> c) ==> c)),
     [then forall_i (bind (T --> prop) x12 \ then (conv (land_tac dd)) (then i h))])
 , theorem exists_i (pi T \ (! f \ ! w \ f ' w ==> (exists '' T ' f)),
    [then forall_i
     (bind (T --> prop) x12 \
       then forall_i
        (bind T x13 \
          then i
           (then (conv dd)
             (then forall_i
               (bind prop x14 \ then i (then (lforall x13) (then apply h)))))))])
  , theorem eq_to_impl
     ((! x13 \ ! x14 \ (x13 = x14) = ((x13 ==> x14) && (x14 ==> x13))),
     [thenl inv [(bind prop x13 \ bind prop x14 \ then (conv (then sym h)) h),
       (bind prop x13 \ bind prop x14 \ then (conv h) h),
       (bind prop x13 \ bind prop x14 \ itaut 2),
       (bind prop x13 \ bind prop x14 \ itaut 2)]])

 /*********** Axiomatization of disjoint union ********/
  , decl inj1_disj_union (pi A \pi B \ A --> disj_union '' A '' B)
  , decl inj2_disj_union (pi A \ pi B \ B --> disj_union '' A '' B)
  , decl case_disj_union (pi A \pi B \ pi C \ disj_union '' A '' B --> (A --> C) --> (B --> C) --> C)
  , axiom case_disj_union_inj1 (pi A \ pi B \ pi C \ (! b \ ! (A --> C) e1 \ ! (B --> C) e2  \
    case_disj_union '' A '' B '' C ' (inj1_disj_union '' A '' B ' b) ' e1 ' e2 = e1 ' b))
  , axiom case_disj_union_inj2 (pi A \ pi B \ pi C \ (! b \ ! (A --> C) e1 \ ! (B --> C) e2  \
    case_disj_union '' A '' B '' C ' (inj2_disj_union '' A '' B ' b) ' e1 ' e2 = e2 ' b))

 /*********** Axiomatization of the universe ********/
 , decl injection_univ (pi A \pi B \ A --> univ '' A '' B)
 , decl ejection_univ (pi A \pi B \ univ '' A '' B --> A)
 , decl inject_limit_univ (pi A \pi B \ (B --> univ '' A '' B) --> univ '' A '' B)
 , decl eject_limit_univ (pi A \ pi B \ univ '' A '' B --> (B --> univ '' A '' B))
 , decl pair_univ (pi A \pi B \ univ '' A '' B --> univ '' A '' B --> univ '' A '' B)
 , decl proj1_univ (pi A \ pi B \ univ '' A '' B --> univ '' A '' B)
 , decl proj2_univ (pi A \pi B \ univ '' A '' B --> univ '' A '' B)
 , decl inj1_univ (pi A \pi B \ univ '' A '' B --> univ '' A '' B)
 , decl inj2_univ (pi A \pi B \ univ '' A '' B --> univ '' A '' B)
 , decl case_univ (pi A \pi B \ pi C \ univ '' A '' B --> (univ '' A '' B --> C) --> (univ '' A '' B --> C) --> C)
 , axiom ejection_injection_univ (pi A \ pi B \
    ! A p \ ejection_univ '' A '' B ' (injection_univ '' A '' B ' p) = p)
 , axiom eject_inject_limit_univ (pi A \ pi B \
    ! (B --> univ '' A '' B) p \ eject_limit_univ '' A '' B ' (inject_limit_univ '' A '' B ' p) = p)
 , axiom proj1_pair_univ (pi A \ pi B \ ! (univ '' A '' B) p1 \ ! p2 \
    proj1_univ '' A '' B ' (pair_univ '' A '' B ' p1 ' p2) = p1)
 , axiom proj2_pair_univ (pi A \ pi B \ ! p1 \ ! (univ '' A '' B) p2 \
    proj2_univ '' A '' B ' (pair_univ '' A '' B ' p1 ' p2) = p2)
 , axiom case_univ_inj1 (pi A \ pi B \ pi C \ (! b \ ! (univ '' A '' B --> C) e1 \ ! e2  \
    case_univ '' A '' B '' C ' (inj1_univ '' A '' B ' b) ' e1 ' e2 = e1 ' b))
 , axiom case_univ_inj2 (pi A \ pi B \ pi C \ (! b \ ! (univ '' A '' B --> C) e1 \ ! e2 \
    case_univ '' A '' B '' C ' (inj2_univ '' A '' B ' b) ' e1 ' e2 = e2 ' b))

 /******************* Equality *****************/
 , theorem eq_reflexive (pi A \ ((! A a \ a = a),
   [ then forall_i (bind A x \ r) ]))

 /******************* Logic *****************/
 , theorem or_commutative ((! a \ ! b \ a $$ b <=> b $$ a),
   [itaut 1])
 , theorem or_ff ((! a \ a $$ ff <=> a),
   [itaut 1])
 , theorem or_tt ((! a \ a $$ tt <=> tt),
   [itaut 1])
 , theorem or_idempotent ((! a \ a $$ a <=> a),
   [itaut 1])
 , theorem or_associative ((! a \ ! b \ ! c \ a $$ (b $$ c) <=> (a $$ b) $$ c),
   [itaut 1])
 , theorem and_commutative ((! a \ ! b \ a && b <=> b && a),
   [itaut 1])
 , theorem and_tt ((! a \ a && tt <=> a),
   [itaut 1])
 , theorem and_ff ((! a \ a && ff <=> ff),
   [itaut 1])
 , theorem and_idempotent ((! a \ a && a <=> a),
   [itaut 1])
 , theorem and_associative ((! a \ ! b \ ! c \ a && (b && c) <=> (a && b) && c),
   [itaut 1])
 , theorem and_or ((! a \ ! b \ ! c \ a && (b $$ c) <=> (a && b) $$ (a && c)),
   [itaut 1])
 , theorem or_and ((! a \ ! b \ ! c \ a $$ (b && c) <=> (a $$ b) && (a $$ c)),
   [itaut 1])
 , theorem ads_or_and ((! a \ ! b \ (a && b) $$ b <=> b),
   [itaut 1])
 , theorem ads_and_or ((! a \ ! b \ (a $$ b) && b <=> b),
   [itaut 1])
 , theorem not_or ((! a \ ! b \ not ' a && not ' b <=> not ' (a $$ b)),
   [itaut 2])
 , theorem not_and ((! a \ ! b \ not ' a $$ not ' b ==> not ' (a && b)),
   [itaut 2])
 , theorem not_not_not ((! p \ not ' (not ' (not ' p)) <=> not ' p),
   [itaut 3])
 , theorem impl_not_not ((! a \ ! b \ (a ==> b) ==> (not ' b ==> not ' a)),
   [itaut 3])
 , theorem eq_to_impl_f ((! p \ ! q \ (p <=> q) ==> p ==> q),
    [itaut 2])
 , theorem eq_to_impl_b ((! p \ ! q \ (p <=> q) ==> q ==> p),
    [itaut 2])

/*************** Properties inj/disj/univ ***********/
 , theorem pair_univ_inj_l 
   (pi A \ pi B \ (! (univ '' A '' B) x20 \ ! x21 \ ! x22 \ ! x23 \ pair_univ '' A '' B ' x20 ' x22 = pair_univ '' A '' B ' x21 ' x23 ==> x20 = x21) ,
   [then (repeat forall_i)
     (bind (univ '' A '' B) x22 \
       bind (univ '' A '' B) x23 \
        bind (univ '' A '' B) x24 \
         bind (univ '' A '' B) x25 \
          then i
           (then (cutth proj1_pair_univ)
             (then (lforall x22)
               (then (conv (land_tac (then sym apply)))
                 (then (conv (depth_tac h)) (applyth proj1_pair_univ))))))])
 , theorem pair_univ_inj_r 
   (pi A \ pi B \ (! (univ '' A '' B) x20 \ ! x21 \ ! x22 \ ! x23 \ pair_univ '' A '' B ' x20 ' x22 = pair_univ '' A '' B ' x21 ' x23 ==> x22 = x23) ,
   [then (repeat forall_i)
     (bind (univ '' A '' B) x22 \
       bind (univ '' A '' B) x23 \
        bind (univ '' A '' B) x24 \
         bind (univ '' A '' B) x25 \
          then i
           (then (cutth proj2_pair_univ)
             (then (lforall x22)
               (then (conv (land_tac (then sym apply)))
                 (then (conv (depth_tac h)) (applyth proj2_pair_univ))))))])
 , theorem injection_univ_inj
   (pi A \ pi B \ (! A x20 \ ! x21 \ injection_univ '' A '' B ' x20 = injection_univ '' A '' B ' x21 ==> x20 = x21) ,
    [then forall_i
     (bind A x20 \
       then forall_i
        (bind A x21 \
          then (then (cutth ejection_injection_univ) (lforall x21))
           (then (then (cutth ejection_injection_univ) (lforall x20))
             (then i
               (thenl
                 (cut
                   (ejection_univ '' A '' B ' (injection_univ '' A '' B ' x20) =
                     ejection_univ '' A '' B ' (injection_univ '' A '' B ' x21)))
                 [thenl
                   (cut
                     ((ejection_univ '' A '' B ' (injection_univ '' A '' B ' x20) =
                        ejection_univ '' A '' B ' (injection_univ '' A '' B ' x21)) =
                       (x20 = x21)))
                   [then (conv (depth_tac (then sym h))) h,
                   thenl c [thenl c [r, h], h]], thenl c [r, h]])))))])
 , theorem inj1_univ_inj
   (pi A \ pi B \ (! (univ '' A '' B) x20 \ ! x21 \ inj1_univ '' A '' B ' x20 = inj1_univ '' A '' B ' x21 ==> x20 = x21) ,
    [then inv
     (bind (univ '' A '' B) x20 \ bind (univ '' A '' B) x21 \
        thenl (t (case_univ '' A '' B '' (univ '' A '' B) ' (inj1_univ '' A '' B ' x20) '
             (lam (univ '' A '' B) x22 \ x22) '
             (lam (univ '' A '' B) x22 \ x22)))
         [then sym
           (then (conv (land_tac (applyth case_univ_inj1)))
             (then (conv (land_tac b)) r)),
         then (conv (depth_tac h))
          (then (conv (land_tac (applyth case_univ_inj1)))
            (then (conv (land_tac b)) r))])])
 , theorem inj2_univ_inj
   (pi A \ pi B \ (! (univ '' A '' B) x22 \ ! x23 \ inj2_univ '' A '' B ' x22 = inj2_univ '' A '' B ' x23 ==> x22 = x23) ,
    [then inv
     (bind (univ '' A '' B) x20 \ bind (univ '' A '' B) x21 \
        thenl (t (case_univ '' A '' B '' (univ '' A '' B) ' (inj2_univ '' A '' B ' x20) '
             (lam (univ '' A '' B) x22 \ x22) '
             (lam (univ '' A '' B) x22 \ x22)))
         [then sym
           (then (conv (land_tac (applyth case_univ_inj2)))
             (then (conv (land_tac b)) r)),
         then (conv (depth_tac h))
          (then (conv (land_tac (applyth case_univ_inj2)))
            (then (conv (land_tac b)) r))])])
 , theorem not_eq_inj1_inj2_univ 
   (pi A \ pi B \ (! (univ '' A '' B) x22 \ ! x23 \ inj1_univ '' A '' B ' x22 = inj2_univ '' A '' B ' x23 ==> ff) ,
    [then inv
     (bind (univ '' A '' B) x22 \
       bind (univ '' A '' B) x23 \
        then (cutth case_univ_inj1)
         (then (lforall x22)
           (then (lforall (lam (univ '' A '' B) x24 \ ff))
             (then (lforall (lam (univ '' A '' B) x24 \ tt))
               (thenl (m ((lam (univ '' A '' B) x24 \ ff) ' x22)) [b,
                 then (conv (then sym h))
                  (then (wl [])
                    (then (conv (depth_tac h))
                      (then (wl [])
                        (then (conv (applyth case_univ_inj2))
                          (then (conv b) (itaut 1))))))])))))])
 , theorem inj1_disj_union_inj (pi A \ pi B \
    ((! x \ ! y \
     inj1_disj_union '' A '' B ' x = inj1_disj_union '' A '' B ' y ==> x = y) ,
    [then inv
      (bind A x23 \
        bind A x24 \
         then (cutth case_disj_union_inj1)
          (then (lforall x23)
            (then (lforall (lam A x25 \ x25))
              (then (lforall (lam B x25 \ choose '' A))
                (thenl (t ((lam A x25 \ x25) ' x23))
                  [then (conv (rand_tac b)) r,
                  then (conv (land_tac (then sym h)))
                   (then (wl [])
                     (then (conv (depth_tac h))
                       (then (wl [])
                         (then (conv (land_tac (applyth case_disj_union_inj1)))
                           b))))])))))]))
 , theorem inj2_disj_union_inj (pi A \ pi B \
    ((! x \ ! y \
     inj2_disj_union '' A '' B ' x = inj2_disj_union '' A '' B ' y ==> x = y) ,
    [then inv
      (bind B x23 \
        bind B x24 \
         then (cutth case_disj_union_inj2)
          (then (lforall x23)
            (then (lforall (lam A x25 \ choose '' B))
              (then (lforall (lam B x25 \ x25))
                (thenl (t ((lam B x25 \ x25) ' x23))
                  [then (conv (rand_tac b)) r,
                  then (conv (land_tac (then sym h)))
                   (then (wl [])
                     (then (conv (depth_tac h))
                       (then (wl [])
                         (then (conv (land_tac (applyth case_disj_union_inj2)))
                           b))))])))))]))

 /********** Monotonicity of logical connectives *********/
 , theorem and_monotone ((! a1 \ ! b1 \ ! a2 \ ! b2 \
    (a1 ==> b1) ==> (a2 ==> b2) ==> a1 && a2 ==> b1 && b2),
    [itaut 2])
 , theorem or_monotone ((! a1 \ ! b1 \ ! a2 \ ! b2 \
    (a1 ==> b1) ==> (a2 ==> b2) ==> a1 $$ a2 ==> b1 $$ b2),
    [itaut 2])
 , theorem impl_monotone ((! a1 \ ! b1 \ ! a2 \ ! b2 \
    (b1 ==> a1) ==> (a2 ==> b2) ==> (a1 ==> a2) ==> (b1 ==> b2)),
    [itaut 3])
 , theorem not_monotone ((! p \ ! q \ (p ==> q) ==> (not ' q) ==> (not ' p)),
    [itaut 3])
 , theorem forall_monotone (pi A \ (! p \ ! q \
    (! A x \ p ' x ==> q ' x) ==> (! x \ p ' x) ==> (! x \ q ' x)),
    [itaut 6])
 , theorem exists_monotone (pi A \ (! p \ ! q \
    (! A x \ p ' x ==> q ' x) ==> (? x \ p ' x) ==> (? x \ q ' x)),
    [itaut 6])

 /********** Knaster-Tarski theorem *********/
  , def in (pi A \ (A --> (A --> prop) --> prop),
     (lam A x \ lam (A --> prop) j \ j ' x))
  , def subseteq (pi A \ ((A --> prop) --> (A --> prop) --> prop),
     (lam (A --> prop) x \ lam (A --> prop) y \ ! z \ z #in x ==> z #in y))
  , theorem in_subseteq (pi A \ 
     (! s \ ! t \ ! x \ s <<= t ==> x #in s ==> x #in t),
     [then forall_i
       (bind (A --> prop) x9 \
         then forall_i
          (bind (A --> prop) x10 \
            then forall_i (bind A x11 \ then (conv (land_tac dd)) (itaut 4))))])
  , def monotone (pi A \ (((A --> prop) --> (A --> prop)) --> prop),
      (lam (_ A) f \ ! x \ ! y \ x <<= y ==> f ' x <<= f ' y))
  , def is_fixpoint (pi A \ (((A --> prop) --> (A --> prop)) --> ((A --> prop) --> prop)),
     (lam (_ A) f \ lam (_ A) x \ (f ' x) <<= x && x <<= (f ' x)))
  , def fixpoint (pi A \ (((A --> prop) --> (A --> prop)) --> (A --> prop)),
     (lam (_ A) f \ lam A a \ ! e \ f ' e <<= e ==> a #in e))
  , theorem fixpoint_subseteq_any_prefixpoint (pi A \
     (! f \ ! x\ f ' x <<= x ==> fixpoint '' A ' f <<= x),
     [then inv
       (bind ((A --> prop) --> (A --> prop)) x9 \
         (bind (A --> prop) x10 \
           then (conv (land_tac dd))
            (then (conv dd)
              (then forall_i
                (bind A x11 \
                  then (conv (land_tac dd))
                   (then (conv (land_tac b)) (itaut 4)))))))])
  , theorem fixpoint_subseteq_any_fixpoint (pi A \
     (! f \ ! x\ is_fixpoint '' A ' f ' x ==> fixpoint '' A ' f <<= x),
     [then forall_i
       (bind ((A --> prop) --> (A --> prop)) x9 \
         then forall_i
          (bind (A --> prop) x10 \
            then (conv (land_tac dd))
             (then (cutth fixpoint_subseteq_any_prefixpoint) (itaut 8))))])
  , theorem prefixpoint_to_prefixpoint (pi A \
     (! f \ ! x \ monotone '' A ' f ==> f ' x <<= x ==> f ' (f ' x) <<= f ' x),
    [then forall_i
      (bind ((A --> prop) --> (A --> prop)) x9 \
        then forall_i
         (bind (A --> prop) x10 \ then (conv (land_tac dd)) (itaut 6)))])
  , theorem fixpoint_is_prefixpoint (pi A \
     (! f \ monotone '' A ' f ==> f ' (fixpoint '' A ' f)<<= fixpoint '' A ' f),
     [then inv
       (bind ((A --> prop) --> (A --> prop)) x9 \
         then (conv dd)
          (then inv
            (bind A x10 \
              then (conv (depth_tac (dd [fixpoint])))
               (then (conv dd)
                 (then (conv b)
                   (then inv
                     (bind (A --> prop) x11 \
                       thenl (cut (fixpoint '' A ' x9 <<= x11))
                        [thenl
                          (cut (x9 ' (fixpoint '' A ' x9) <<= x9 ' x11))
                          [then (cutth in_subseteq)
                            (then (lforall_last (x9 ' x11))
                              (then (lforall_last x11)
                                (thenl apply_last [h,
                                  then (cutth in_subseteq) (itaut 10)]))),
                          thenl
                           (m (monotone '' A ' x9 ==> x9 ' (fixpoint '' A ' x9) <<= x9 ' x11))
                           [itaut 10, then (conv (land_tac dd)) (itaut 10)]],
                        then (applyth fixpoint_subseteq_any_prefixpoint) h])))))))])
  , theorem fixpoint_is_fixpoint (pi A \
    (! f \ monotone '' A ' f ==> is_fixpoint '' A ' f ' (fixpoint '' A ' f)),
    [then inv
      (bind ((A --> prop) --> (A --> prop)) x9 \
        then (conv (depth_tac (dd [is_fixpoint])))
         (thenl inv [then (applyth fixpoint_is_prefixpoint) h,
           then (applyth fixpoint_subseteq_any_prefixpoint)
            (then (g (monotone '' A ' x9))
              (then (conv (land_tac dd))
                (then inv
                  (then apply (then (applyth fixpoint_is_prefixpoint) h)))))]))])

 /*********** Axiomatization of well-founded recursion ********/
 , decl rec (pi A \pi B \ ((A --> B) --> (A --> B)) --> (A --> B))
 , inductive_def acc accF accF_monotone acc_i0 acc_e0 acc_e
    (pi A \ param (A --> A --> prop) lt \ acc \
     [ (acc_i, ! x \ (! y \ lt ' y ' x ==> acc ' y) ==> acc ' x) ])

 , def well_founded (pi A \ ((A --> A --> prop) --> prop,
    lam (_ A) lt \ ! x \ acc '' A ' lt ' x))

 , axiom rec_is_fixpoint (pi A \ pi B \
   (! lt \ well_founded '' A ' lt ==>
    ! ((A --> B) --> (A --> B)) h \
     (! f \ ! g \ ! i \
       (! p \ lt ' p ' i ==> f ' p = g ' p) ==> h ' f ' i = h ' g ' i) ==>
     rec '' A '' B ' h = h ' (rec '' A '' B ' h)))
 /******************* TESTS *****************/
 /* The first three tests are commented out because they require extra-hacks
    in the kernel to avoid quantifying over p, q and g.
 , theorem test_apply (p ==> (p ==> p ==> q) ==> q,
    [then i (then i (then apply h))])
 , theorem test_apply2 (p ==> (! x \ ! y \ x ==> x ==> y) ==> q,
    [then i (then i (then apply h))])
 , theorem test_itaut_1 (((? x \ g x) ==> ! x \ (! y \ g y ==> x) ==> x),
   [itaut 4])*/
 , theorem test_monotone1 (monotone '' _ ' (lam _ p \ lam _ x \ not ' (p ' x) ==> tt && p ' tt $$ p ' x),
   [ auto_monotone ])
 , theorem test_monotone2 (monotone '' _ ' (lam _ p \ lam _ x \ ? z \ not ' (p ' x) ==> tt && p ' tt $$ z),
   [ auto_monotone ])
 , theorem test_monotone3 (monotone '' _ ' (lam _ p \ lam _ x \ ! z \ ? y \ (not ' (p ' x) ==> z && p ' y $$ y)),
   [ auto_monotone ])
 , inductive_def pnn pnnF pnnF_monotone pnn_i pnn_e0 pnn_e (pnn \
     [ (pnn_tt, pnn ' tt)
     , (pnn_not, ! x \ pnn ' x ==> pnn ' (not ' x))])
 , theorem pnn_e
    ((! x13 \
       x13 ' tt && (! x14 \ x13 ' x14 ==> x13 ' (not ' x14)) ==>
        (! x14 \ pnn ' x14 ==> x13 ' x14)) ,
   [then forall_i
     (bind (prop --> prop) x13 \
       then (cutth pnn_e0)
        (then (lforall x13)
          (then i
            (thenl lapply
              [then (conv (depth_tac (dd [pnnF])))
                (then forall_i
                  (bind prop x14 \
                    then i
                     % from now on the proof is ad-hoc + fragile
                     (thenl left [then (conv (depth_tac h)) (itaut 1),
                       then left
                        (bind prop x15 \
                          then left (then (conv (depth_tac h)) (itaut 8)))]))),
              h]))))])
 , theorem pnn_has_two_values
    ((! x13 \ pnn ' x13 ==> x13 = tt $$ x13 = ff) ,
    % applying an elimination principle is hard: it should be automatized
    [then (cutth pnn_e)
      (then (lforall (lam prop x13 \ or ' (eq '' prop ' x13 ' tt) ' (eq '' prop ' x13 ' ff)))
        (thenl lapply
          [thenl conj [then (conv b) (itaut 1),
            then (repeat (conv (depth_tac b)))
             (then forall_i (bind prop x13 \ then i (then left (itaut 8))))],
          then inv
           (bind prop x13 \
             then (lforall x13)
              (thenl lapply [h,
                then
                 (g
                   ((lam prop x14 \ or ' (eq '' prop ' x14 ' tt) ' (eq '' prop ' x14 ' ff)) '
                     x13))
                 (then (repeat (conv (depth_tac b)))
                   (then
                     (w
                       ((lam prop x14 \ or ' (eq '' prop ' x14 ' tt) ' (eq '' prop ' x14 ' ff))
                         ' x13)) (then (w (pnn ' x13)) (itaut 2))))]))]))])
 , inductive_def in_two in_twoF in_twoF_monotone in_two_i in_two_e0 in_two_e (in_two \
     [ (in_two_tt, in_two ' tt)
     , (in_two_ff, in_two ' ff) ])
 , new_basic_type bool2 myrep2 myabs2 myrepabs2 myabsrep2 myproprep2
    (pnn,
    [then (cutth pnn_tt) (then (applyth exists_i) h)])
 , def mytt (bool2,(myabs2 ' tt))
 , def mynot ((bool2 --> bool2),(lam _ x \ myabs2 ' (not ' (myrep2 ' x))))
 , theorem mytt_transfer
   (myrep2 ' mytt = tt ,
     [then (conv (depth_tac (dd [mytt])))
       (then (applyth myrepabs2) (applyth pnn_tt))])
 , theorem mynot_transfer
   ((! x18 \ myrep2 ' (mynot ' x18) = not ' (myrep2 ' x18)) ,
     [then (conv (depth_tac (dd [mynot])))
       (then forall_i
         (bind bool2 x18 \
           then (applyth myrepabs2)
            (then (applyth pnn_not) (applyth myproprep2))))])
 , theorem mybool2_e
 ((! x18 \
    x18 ' mytt && (! x19 \ x18 ' x19 ==> x18 ' (mynot ' x19)) ==>
     (! x19 \ x18 ' x19)) ,
   [thenl
     (cut
       (forall '' (bool2 --> prop) '
         (lam (bool2 --> prop) x18 \
           impl '
            (and ' (x18 ' (myabs2 ' (myrep2 ' mytt))) '
              (forall '' bool2 '
                (lam bool2 x19 \
                  impl ' (x18 ' (myabs2 ' (myrep2 ' x19))) '
                   (x18 '
                     (myabs2 '
                       (myrep2 ' (mynot ' (myabs2 ' (myrep2 ' x19)))))))))
            '
            (forall '' bool2 '
              (lam bool2 x19 \ x18 ' (myabs2 ' (myrep2 ' x19)))))))
     [then
       (g
         (forall '' (bool2 --> prop) '
           (lam (bool2 --> prop) x18 \
             impl '
              (and ' (x18 ' (myabs2 ' (myrep2 ' mytt))) '
                (forall '' bool2 '
                  (lam bool2 x19 \
                    impl ' (x18 ' (myabs2 ' (myrep2 ' x19))) '
                     (x18 '
                       (myabs2 '
                         (myrep2 ' (mynot ' (myabs2 ' (myrep2 ' x19)))))))))
              '
              (forall '' bool2 '
                (lam bool2 x19 \ x18 ' (myabs2 ' (myrep2 ' x19)))))))
       (then
         (w
           (forall '' (bool2 --> prop) '
             (lam (bool2 --> prop) x18 \
               impl '
                (and ' (x18 ' (myabs2 ' (myrep2 ' mytt))) '
                  (forall '' bool2 '
                    (lam bool2 x19 \
                      impl ' (x18 ' (myabs2 ' (myrep2 ' x19))) '
                       (x18 '
                         (myabs2 '
                           (myrep2 ' (mynot ' (myabs2 ' (myrep2 ' x19)))))))))
                '
                (forall '' bool2 '
                  (lam bool2 x19 \ x18 ' (myabs2 ' (myrep2 ' x19)))))))
         (then (repeat (conv (depth_tac (applyth myabsrep2)))) (then i h))),
     then forall_i
      (bind (bool2 --> prop) x18 \
        then (cutth pnn_e)
         (then
           (lforall
             (lam prop x19 \
               exists '' bool2 '
                (lam bool2 x20 \
                  and ' (eq '' _ ' x19 ' (myrep2 ' x20)) '
                   (x18 ' (myabs2 ' x19)))))
           (then inv
             (bind bool2 x19 \
               thenl
                (cut
                  ((lam prop x20 \
                     exists '' bool2 '
                      (lam bool2 x21 \
                        and ' (eq '' _ ' x20 ' (myrep2 ' x21)) '
                         (x18 ' (myabs2 ' x20)))) ' (myrep2 ' x19)))
                [then
                  (g
                    ((lam prop x20 \
                       exists '' bool2 '
                        (lam bool2 x21 \
                          and ' (eq '' _ ' x20 ' (myrep2 ' x21)) '
                           (x18 ' (myabs2 ' x20)))) ' (myrep2 ' x19)))
                  (then (conv (depth_tac b)) inv),
                thenl apply
                 [then (repeat (conv (depth_tac b)))
                   (thenl inv
                     [then (cutth exists_i)
                       (then
                         (lforall_last
                           (lam bool2 x20 \
                             and ' (eq '' _ ' tt ' (myrep2 ' x20)) '
                              (x18 ' (myabs2 ' tt))))
                         (then (lforall_last mytt)
                           (then apply_last (then (conv b)
                            (thenl inv
                             [then (cutth mytt_transfer)
                               (then (conv (depth_tac h)) (applyth tt_intro)),
                             (applyth tt_intro),
                             then (cutth mytt_transfer)
                              (then (g (x18 ' (myabs2 ' (myrep2 ' mytt))))
                                (then (conv (depth_tac h)) (then i h)))]))))),
                     (bind prop x20 \
                       bind bool2 x21 \
                        then (cutth exists_i)
                         (then
                           (lforall_last
                             (lam bool2 x22 \
                               and ' (eq '' _ ' (not ' x20) ' (myrep2 ' x22)) '
                                (x18 ' (myabs2 ' (not ' x20)))))
                           (then (lforall_last (mynot ' x21))
                             (then apply_last (then (conv b)
    (thenl inv
     [then (conv (applyth mynot_transfer))
       (then (conv (depth_tac (dd [not]))) (then inv (itaut 3))),
     then (g (myrep2 ' (mynot ' x21)))
      (then (conv (land_tac (applyth mynot_transfer)))
        (then (conv (depth_tac (dd [not]))) (then inv (itaut 3)))),
     then (lforall (myabs2 ' x20))
      (thenl lapply [then (conv (depth_tac (applyth myabsrep2))) h,
        then
         (g
           (x18 '
             (myabs2 '
               (myrep2 ' (mynot ' (myabs2 ' (myrep2 ' (myabs2 ' x20))))))))
         (then (conv (depth_tac (applyth myabsrep2)))
           (then (conv (depth_tac (applyth myabsrep2)))
             (thenl (cut (x20 = myrep2 ' x21))
               [then (conv (depth_tac h))
                 (then (conv (depth_tac h))
                   (then (conv (depth_tac (applyth myabsrep2)))
                     (then i
                       (then
                         (conv
                           (rand_tac
                             (rand_tac (then sym (applyth mynot_transfer)))))
                         (then (conv (depth_tac (applyth myabsrep2))) h))))),
               itaut 2])))])]))))))]),
                 applyth myproprep2]]))))]])

, theorem step0
    ((! x13 \ mynot ' (mynot ' (mynot ' x13)) = mynot ' x13) ,
     [then inv
      (bind bool2 x13 \
        then (repeat (conv (depth_tac (dd [mynot]))))
         (thenl (conv (land_tac (rand_tac (rand_tac (applyth myrepabs2)))))
          [then (cutth pnn_not)
            (then (lforall (myrep2 ' (myabs2 ' (not ' (myrep2 ' x13)))))
              (then (cutth myproprep2)
                (then (lforall (myabs2 ' (not ' (myrep2 ' x13))))
                  (then apply h)))),
          thenl
           (conv
             (land_tac
               (rand_tac (rand_tac (rand_tac (applyth myrepabs2))))))
           [then (cutth pnn_not)
             (then (lforall (myrep2 ' x13))
               (then (cutth myproprep2)
                 (then (lforall x13) (then apply h)))),
           then (conv (land_tac (rand_tac (applyth not_not_not)))) r]]))])
 , theorem mynot_mynot_mytt
    (mynot ' (mynot ' mytt) = mytt ,
     [then (conv (depth_tac (dd [mynot])))
      (then (cutth mynot_transfer)
        (then (lforall mytt)
          (then (conv (depth_tac h))
            (then (cutth mytt_transfer)
              (then (conv (depth_tac h))
                (then (conv (depth_tac (dd [mytt]))) (thenl c [r, itaut 3])))))))])
 , theorem step1
    ((! x18 \ x18 = mytt $$ x18 = mynot ' mytt) ,
     [then forall_i
      (bind bool2 x18 \
       then (cutth mybool2_e)
        (thenl
          (cut
            ((lam bool2 x19 \
               or ' (eq '' _ ' x19 ' mytt) ' (eq '' _ ' x19 ' (mynot ' mytt))) ' x18))
          [then
            (g
              ((lam bool2 x19 \
                 or ' (eq '' _ ' x19 ' mytt) ' (eq '' _ ' x19 ' (mynot ' mytt))) '
                x18)) (then (conv (depth_tac b)) (then i h)),
          then apply
           (then (repeat (conv (depth_tac b)))
             (thenl conj [then (applyth orl) r,
               thenl inv
                [(bind bool2 x19 \
                   then (applyth orr) (then (conv (depth_tac h)) r)),
                (bind bool2 x19 \
                  then (applyth orl) (then (conv (depth_tac h)) (applyth mynot_mynot_mytt)))]]))]))])

 /******* Cartesian product of types ******/
 /* TODO: this is an inductive type as well: generalize
    inductive_type to type abstractions */
 , def is_pair (pi A \ pi B \
  (univ '' (disj_union '' A '' B) '' prop --> prop),
  lam (_ A B) p \ ? A a \ ? B b \
   p =
    pair_univ '' (_ A B) '' _ '
     (injection_univ '' (_ A B) '' _ ' (inj1_disj_union '' A '' B ' a)) '
     (injection_univ '' (_ A B) '' _ ' (inj2_disj_union '' A '' B ' b)))
 , new_basic_type prod prod_rep prod_abs prod_repabs prod_absrep prod_proprep
    (pi A \ pi B \ is_pair '' A '' B, [daemon])
 , def pair (pi A \ pi B \
    (A --> B --> prod '' A '' B,
    lam A a \ lam B b \
     prod_abs '' A '' B '
      (pair_univ '' (_ A B) '' _ '
       (injection_univ '' (_ A B) '' _ ' (inj1_disj_union '' A '' B ' a)) '
       (injection_univ '' (_ A B) '' _ ' (inj2_disj_union '' A '' B ' b)))
    ))
 /* TODO: define fst and snd and prove the usual lemmas
    fst ' (pair ' a ' b) = a */

  /************* Natural numbers ***************/
 , inductive_def is_nat is_natF is_nat_monotone is_nat_i is_nat_e0 is_nat_e
   (is_nat \
     [ (is_nat_z, is_nat ' (inj1_univ '' prop '' prop ' (injection_univ '' prop '' prop ' ff)))
     , (is_nat_s, ! x \ is_nat ' x ==> is_nat ' (inj2_univ '' prop '' prop ' x))])
 , new_basic_type nat nat_rep nat_abs nat_repabs nat_absrep nat_proprep
    (is_nat,
    [then (cutth is_nat_z) (then (applyth exists_i) h)])
 , def z (nat, nat_abs ' (inj1_univ '' prop '' prop ' (injection_univ '' prop '' prop ' ff)))
 , def s (nat --> nat,
    (lam _ x \ nat_abs ' (inj2_univ '' prop '' prop ' (nat_rep ' x))))
 /* TODO: consequence of is_nat_e by transfer principles */
 , theorem nat_e ((! p \ p ' z ==> (! n \ p ' n ==> p ' (s ' n)) ==> ! n \ p ' n), [ daemon ])
 , theorem nat_abs_inj
   ((! x18 \
      ! x19 \
       is_nat ' x18 ==>
        is_nat ' x19 ==> nat_abs ' x18 = nat_abs ' x19 ==> x18 = x19) ,
     [then inv
       (bind _ x18 \
         bind _ x19 \
          thenl (conv (land_tac (then sym (applyth nat_repabs)))) [h,
           thenl (conv (rand_tac (then sym (applyth nat_repabs)))) [h,
            then (conv (depth_tac h)) r]])])
 , theorem nat_rep_inj
   ((! x18 \ ! x19 \ nat_rep ' x18 = nat_rep ' x19 ==> x18 = x19) ,
     [then inv
       (bind nat x18 \
         bind nat x19 \
          then (conv (land_tac (then sym (applyth nat_absrep))))
           (then (conv (rand_tac (then sym (applyth nat_absrep))))
             (then (conv (depth_tac h)) r)))])
 , theorem s_inj ((! x18 \ ! x19 \ s ' x18 = s ' x19 ==> x18 = x19) ,
     [then (repeat (conv (depth_tac (dd [s]))))
       (then inv
         (bind nat x18 \
           bind nat x19 \
            then (applyth nat_rep_inj)
             (then (applyth inj2_univ_inj)
               (thenl (applyth nat_abs_inj)
                 [then (applyth is_nat_s) (applyth nat_proprep),
                 then (applyth is_nat_s) (applyth nat_proprep), h]))))])
 , theorem not_equal_z_s ((! x20 \ not ' (z = s ' x20)) ,
     [then (repeat (conv (depth_tac (dd [z]))))
       (then (repeat (conv (depth_tac (dd [s]))))
         (then (repeat (conv (depth_tac (dd [not]))))
           (then inv
             (bind nat x20 \
               then (applyth not_eq_inj1_inj2_univ)
                (thenl (thenl (applyth nat_abs_inj) [id, id, h])
                  [applyth is_nat_z,
                  then (applyth is_nat_s) (applyth nat_proprep)])))))])
 , def nat_case (pi A \ (nat --> A --> (nat --> A) --> A,
    lam _ n \ lam (_ A) a \ lam (_ A) f \
     case_univ '' prop '' prop '' A ' (nat_rep ' n) ' (lam _ x \ a) ' (lam _ p \ f ' (nat_abs ' p))))
 , theorem nat_case_z (pi A \ ((! x21 \ ! x22 \ nat_case '' A ' z ' x21 ' x22 = x21) ,
      [then (conv (depth_tac (dd [nat_case])))
        (then (conv (depth_tac (dd [z])))
          (then forall_i
            (bind A x21 \
              then forall_i
               (bind (nat --> A) x22 \
                 thenl
                  (conv (land_tac (rator_tac (land_tac (applyth nat_repabs)))))
                  [applyth is_nat_z,
                   then (conv (depth_tac (applyth case_univ_inj1)))
                    (then (conv (depth_tac b)) r)]))))]))
 , theorem nat_case_s
   (pi A \ (! x21 \ ! x22 \ ! x23 \
     nat_case '' A ' (s ' x21) ' x22 ' x23 = x23 ' x21),
     [then (conv (depth_tac (dd [nat_case])))
       (then (conv (depth_tac (dd [s])))
         (then forall_i
           (bind nat x21 \
             then forall_i
              (bind A x22 \
                then forall_i
                 (bind (nat --> A) x23 \
                   thenl
                    (conv (land_tac (rator_tac (land_tac (applyth nat_repabs)))))
                    [then (applyth is_nat_s) (applyth nat_proprep),
                     then (conv (depth_tac (applyth case_univ_inj2)))
                     (then (conv (depth_tac b))
                       (then (conv (depth_tac (applyth nat_absrep))) r))])))))])


 , theorem pred_well_founded
   (well_founded '' nat ' (lam nat x21 \ lam nat x22 \ x22 = s ' x21) ,
   [then (conv dd)
     (then forall_i
       (bind nat x21 \
         thenl (applyth nat_e)
          [then (applyth acc_i)
            (then (repeat (conv (depth_tac b)))
              (then inv
                (bind nat x22 \
                  then (applyth ff_elim) (then (cutth not_equal_z_s) (itaut 4))))),
          then inv
           (bind nat x22 \
             then (applyth acc_i)
              (then (repeat (conv (depth_tac b)))
                (then inv
                  (bind nat x23 \
                    then (cutth s_inj)
                     (then (lforall x22)
                       (then (lforall x23)
                         (thenl lapply [h,
                           then (conv (rand_tac (then sym h))) h])))))))]))])
 , def nat_recF (pi A \
    A --> (nat --> A --> A) --> (nat --> A) --> (nat --> A)
    , lam A a \ lam (_ A) f \ lam (_ A) rec \ lam _ n \
       nat_case '' A ' n ' a ' (lam _ p \ f ' p ' (rec ' p)))
 , def nat_rec (pi A \
    A --> (nat --> A --> A) --> nat --> A
    , lam A a \ lam (_ A) f \ rec '' nat '' A ' (nat_recF '' A ' a ' f))
 , theorem nat_rec_ok0 (pi A \
   ((! a \ ! f \
     nat_rec '' A ' a ' f = nat_recF '' A ' a ' f ' (nat_rec '' A ' a ' f)) ,
   [then inv
     (bind A x22 \
       bind (nat --> A --> A) x23 \
        then (repeat (conv (depth_tac (dd [nat_rec]))))
         (thenl (applyth rec_is_fixpoint) [applyth pred_well_founded,
           then (repeat (conv (depth_tac b)))
            (then (repeat (conv (depth_tac (dd [nat_recF]))))
              (then forall_i
                (bind (nat --> A) x24 \
                  then forall_i
                   (bind (nat --> A) x25 \
                     then (conv (rand_tac beta_expand))
                      (thenl (applyth nat_e)
                        [then (conv (depth_tac b))
                          (then inv
                            (then (conv (land_tac (applyth nat_case_z)))
                              (then (conv (rand_tac (applyth nat_case_z))) r))),
                        then (repeat (conv (depth_tac b)))
                         (then inv
                           (bind nat x26 \
                             then (conv (rand_tac (applyth nat_case_s)))
                              (then (conv (land_tac (applyth nat_case_s)))
                                (then (repeat (conv (depth_tac b)))
                                  (then (lforall x26)
                                    (thenl lapply [r,
                                      then (conv (land_tac (rand_tac h))) r]))))))])))))]))]))
 , theorem nat_rec_ok (pi A \
   (! a \ ! f \ ! n \
     nat_rec '' A ' a ' f ' n =
      nat_case '' A ' n ' a ' (lam _ p \ f ' p ' (nat_rec '' A ' a ' f ' p))),
   [then inv
     (bind A x22 \
       bind (nat --> A --> A) x23 \
        bind nat x24 \
         then (conv (land_tac (rator_tac (applyth nat_rec_ok0))))
          (then (conv (depth_tac (dd [nat_recF]))) r))])

 /************* Arithmetics: plus ***************/
 , def plus (nat --> nat --> nat,
    lam _ n \ lam _ m \
     nat_rec '' _ ' m ' (lam _ p \ lam _ sum \ s ' sum)' n)
 , theorem plus_z ((! n \ z + n = n),
   [then (conv (depth_tac (dd [plus])))
     (then inv
       (bind nat x21 \
         then (conv (land_tac (applyth nat_rec_ok)))
          (then (conv (land_tac (applyth nat_case_z))) r)))])
 , theorem plus_s ((! n \ ! m \  s ' n + m = s ' (n + m)),
   [then (repeat (conv (depth_tac (dd [plus]))))
     (then inv
       (bind nat x21 \
         bind nat x22 \
          then (conv (land_tac (applyth nat_rec_ok)))
           (then (conv (land_tac (applyth nat_case_s)))
             (then (repeat (conv (depth_tac b))) r))))])
 , theorem plus_n_z ((! n \ n + z = n),
   [then (conv (rand_tac beta_expand))
     (thenl (applyth nat_e) [then (conv b) (applyth plus_z),
       then (repeat (conv (depth_tac b)))
        (then inv
          (bind nat x21 \
            then (conv (land_tac (applyth plus_s)))
             (then (conv (depth_tac h)) r)))])])
 , theorem plus_n_s ((! n \ ! m \ n + (s ' m) = s ' (n + m)),
   [then (conv (rand_tac beta_expand))
     (thenl (applyth nat_e)
       [then (conv b)
         (then inv
           (bind nat x21 \ then (repeat (conv (depth_tac (applyth plus_z)))) r)),
       then (repeat (conv (depth_tac b)))
        (then inv
          (bind nat x21 \
            bind nat x22 \
             then (conv (land_tac (applyth plus_s)))
              (thenl c [r,
                then (conv (land_tac apply)) (then sym (applyth plus_s))])))])])
 , theorem plus_comm ((! n \ ! m \ n + m = m + n),
   [then (conv (rand_tac beta_expand))
     (thenl (applyth nat_e)
       [then (conv b)
         (then inv
           (bind nat x21 \
             then (conv (land_tac (applyth plus_z)))
              (then sym (applyth plus_n_z)))),
       then (repeat (conv (depth_tac b)))
        (then inv
          (bind nat x21 \
            bind nat x22 \
             then (conv (land_tac (applyth plus_s)))
              (then sym
                (then (conv (land_tac (applyth plus_n_s)))
                  (thenl c [r, then sym apply])))))])])

 ].

/* Status and dependencies of the tactics:
+dd:
+sym:
+eq_true_intro: (th tt_intro)
+forall_i: dd eq_true_intro
+conj: dd eq_true_intro
+andr: dd tt_intro
+andl: dd tt_intro
+forall_e: sym dd
+mp: andr sym dd
+i: dd andl conj
+cut: andr sym dd i
+cutth: cut
+lapply*: mp
+lforall*: mp forall_e
+apply*: lapply lforall
+applyth: cutth apply*

- f converional sometimes fails
- conv (depth_tac) diverges when applied to terms that contain
  metavariables
- repeat is not implemented using progress, that is not even there
*/

/*
-2.5) in the proof for myprop, at the end I provide the
  witness (and X X) where X remains free (and it is not even pi-quantified).
  If prop was empty, then X could not exist. On the other hand, if X was
  empty, then there would be no need to provide the proof at all.
  In any case, the symptom for X remaining free at the end of a proof is
  one or more goals delayed on it. We never check for them and we have
  no way atm to do that. See bug -3)

-2) the test apply_2 is very slow: why?
    same for the witness for myprop

0) definitions must not be recursive; typing should capture it
   (but not if $delay is commented out...)

0.25) occurr check in bind case still missing :-(

0.50) case AppUvar vs AppUVar in unification is bugged (e.g.)
      X^2 x0 x1 = X^2 x0 x1

2) we need to fix the ELPI problems about handling of metavariables.
 I have already discussed with Enrico about them and he could have a
 shot at them. Namely:
 a) occur check + optimization to avoid it when possible (IN PROGRESS)
 b) unimplemented cases of restriction (IN PROGRESS)

3) once we let metavariables reach the goals, the current HOL-light 
 tactic implementation becomes too fragile. We should let the user 
 refer to hypotheses at least by number if not by name. But we better
 have a bidirectional successor/predecessor via $delay

5) we could implement an automated theorem prover in lambdaProlog
 that works or is interfaced with the HOL-light code. There are
 complete provers like leanCOP 2.0 that are only 10 lines of code,
 but use some Prolog tricks.

6) we should do a small formalization, possibly developing a tactic,
 to prove that everything is working. For example, a decision procedure
 for rings or for linear inequations.

*/
