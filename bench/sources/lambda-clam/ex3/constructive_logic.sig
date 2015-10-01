/*

File: constructive_logic.sig
Author: Louise Dennis / James Brotherston
Description: Logic with equality theory, quantifiers, connectives, methods.
Last Modified: 20th August 2002

*/

sig constructive_logic.

accum_sig logic_eq_constants.

type constructive_logic theory.

%--------------------------------
% Rewrite rules

type    ifthen osyn.

type    assAnd1         rewrite_rule.

type    prop3           rewrite_rule.
type    prop4           rewrite_rule.
type    prop5           rewrite_rule.
type    prop6           rewrite_rule.

type    neg1            rewrite_rule.
type    neg2            rewrite_rule.
type    and1            rewrite_rule.
type    and2            rewrite_rule.

type    or1             rewrite_rule.
type    or2             rewrite_rule.
type    or3             rewrite_rule.

type    imp1            rewrite_rule.
type    imp2            rewrite_rule.

type    iff1            rewrite_rule.

type    neq_eval        rewrite_rule.
type    ifthen1         rewrite_rule.
type    ifthen2         rewrite_rule.

type    idty            rewrite_rule.
type    beta_reduction  rewrite_rule.
type 	beta_idty	rewrite_rule.

%---------------------------------
% Some tautologies
%---------------------------------

type taut1 query.
type taut2 query.

end
