/*
 * Interface to code for recognizing formula categories in Horn 
 * clause logic
 */

sig  hc_syntax. 

accum_sig  logic_types, logic_basic. 

/* an `input' predicate---only its definition is used here */
useonly     atom         form -> o.

/* this predicate is used and its definition may be changed */
type        termp        term -> o.

/* `output' predicates---this module supplies their complete definition */
exportdef   goal         form -> o.
exportdef   def_clause   form -> o.
