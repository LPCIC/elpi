/*
 * Interface to code for simplifying goals based on recognizing 
 * ones that have trivial solutions
 */

sig  goalred.

accum_sig   goaltypes. 

exportdef    goalreduce      goal -> goal -> o.
