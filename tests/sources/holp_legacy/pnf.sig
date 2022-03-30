/* 
 * Interface for code for transforming formulas into prenex normal form
 */

sig  pnf.

accum_sig  logic_types, logic_basic.

/* this predicate definition is used but not changed */
useonly  quant_free   form -> o.

/* this definition changes in this module */
type  termp        term -> o.

/* this definition is exported */
exportdef  prenex     form -> form -> o.
