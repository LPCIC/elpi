/* File listmanip.sig. Signature file for list manipulating predicates
used in the theorem prover */

sig listmanip.

exportdef    member                  A -> (list A) -> o.
exportdef    member_and_rest         A -> (list A) -> (list A) -> o.
exportdef    nth_item                int -> A -> (list A) -> o.
exportdef    nth_item_and_rest       int -> A -> (list A) -> (list A) -> o.
exportdef    member_move_to_end      A -> (list A) -> (list A) -> o.
exportdef    add_to_end              A -> (list A) -> (list A) -> o.

