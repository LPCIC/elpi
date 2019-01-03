/*
 * Interface to the implementation of some tacticals, i.e. methods for 
 * combining primitive tactics to produce derived rules 
 */

sig  tacticals. 

accum_sig  goaltypes.

exportdef    maptac          (goal -> goal -> o) -> goal -> goal -> o.
exportdef    then            (goal -> goal -> o)
                          -> (goal -> goal -> o) -> goal -> goal -> o.
exportdef    orelse          (goal -> goal -> o)
                          -> (goal -> goal -> o) -> goal -> goal -> o.
exportdef    idtac           goal -> goal -> o.
exportdef    repeattac       (goal -> goal -> o) -> goal -> goal -> o.
exportdef    try             (goal -> goal -> o) -> goal -> goal -> o.
exportdef    complete        (goal -> goal -> o) -> goal -> goal -> o.
