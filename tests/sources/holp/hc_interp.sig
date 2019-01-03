/* 
 * Interface to code that implements an interpreter for Horn
 * clause logic
 */

sig  hc_interp. 

accum_sig  logic_types, logic_basic, logic_vocab.

exportdef  hc_interp   (list form) -> form -> o.

