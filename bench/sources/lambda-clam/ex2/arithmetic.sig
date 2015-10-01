/*

File: arithmetic.sig
Author: Louise Dennis
Description: Theory of Natural Numbers
Last Modified: 20th March 2001

*/

sig arithmetic.

accum_sig lclam.
accum_sig mathweb.

type arithmetic theory.


/* SYNTAX CONSTANTS */

type 	undef 	osyn. % maybe this should go somewhere else 
		    	% e.g. a partial functions theory.

% type    nat     osyn.
type	integer osyn.

type    zero         osyn.
type    s            osyn.
type    plus         osyn.
type    minus        osyn.
type    otimes        osyn.
type    exp          osyn.
type    lt           osyn.
type    leq          osyn.
type    half         osyn.
type    double       osyn.
type    even         osyn.
type 	pred	     osyn.
type	fun_compose	osyn.
type	fun_iter	osyn.
type	less		osyn.

type	pred1		rewrite_rule.
type	pred2		rewrite_rule.
type    plus1           rewrite_rule.
type    plus2           rewrite_rule.
type    times1          rewrite_rule.
type    times2          rewrite_rule.
type    exp1            rewrite_rule.
type    exp2            rewrite_rule.
type    s_functional    rewrite_rule.
type    leq1            rewrite_rule.
type    leq2            rewrite_rule.
type    leq_ss            rewrite_rule.
type 	leq_transitive	rewrite_rule.
type    p1              rewrite_rule.
type    p2              rewrite_rule.
type    neq_s_zero      rewrite_rule.
type    neq_zero_s      rewrite_rule.
type	less1		rewrite_rule.
type	less2		rewrite_rule.
type	less3		rewrite_rule.
type	less_transitive		rewrite_rule.


type    half1   rewrite_rule.
type    half2   rewrite_rule.
type    half3   rewrite_rule.
type    double1   rewrite_rule.
type    double2   rewrite_rule.
type    even1   rewrite_rule.
type    even2   rewrite_rule.
type    even3   rewrite_rule.

type	fun_iter1	rewrite_rule.
type	fun_iter2	rewrite_rule.
type	fun_iter3	rewrite_rule.
type	fun_compose1	rewrite_rule.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  INDUCTION SCHEMES FOR NAT
%%

type nat_struct         scheme.
type twostep        scheme.
/* type nat_minus          scheme.
type s_to_ss_ind        scheme.
*/

/*  GOALS  */

type eqzero	    query.
type simple         query.
type simple_taut    query.
type assp           query.
type comm           query.
type comp           query.
type falsearith	    query.
type plus2right	    query.
type dist           query.
type distr          query.
type assm           query.
type assp_sy        query.
type expplus        query.
type exptimes       query.
type leqrefl        query.
type leqsuc         query.
type leqsum	    query.
type doublehalf	    query.
type halfplus       query.
type plus1lem	    query.
type plusxx         query.
type zeroplus       query.
type zerotimes       query.
type doubleplus     query.
type halfdouble     query.
type doubletimes    query.
type doubletimes2    query.
type times2right    query.

end
