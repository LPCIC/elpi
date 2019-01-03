/*
 * A harness for testing an interpreter for a logic programming 
 * language based on Horn clauses
 */

module  hcinterp_examples.

accumulate  hc_interp.

accum_sig  logic_basic. 

type   prog  (list form) -> o.

prog ((adj a b) :: (adj b c) :: (adj c (f c)) ::
      (all X\ (all Y\ ((adj X Y) imp (path X Y))))  ::
      (all X\ (all Y\ (all Z\ ( ((adj X Y) and (path Y Z)) 
                                           imp (path X Z))))) :: nil).

pathfroma X :- prog Cs, hc_interp Cs (path a X).

