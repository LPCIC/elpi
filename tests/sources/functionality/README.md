# Functionality

## About the tests

### Success

- test2.elpi: functional ctx + functional premises (FO)
- test4.elpi: loading local clauses (with and without local pi)
- test6.elpi: nested local clauses
- test12.elpi: non overlapping heads using uvar keyword
- test15.elpi: non functional premise followed by bang
- test16.elpi: non functional premise using variable not used in the head
- test17.elpi: functional predicate with functional argument + nested
- test20.elpi: functional predicate with non functional argument declaration
- test22.elpi: functional ho output of a premise used to build the output of the rule
- test28.elpi: non functional prop in functional ctx call (do')
- test29.elpi: similar to previous
- test32.elpi: check functional output
- test36.elpi: predicate with functional output + cut + call to the output
- test39.elpi: functional output with pi quantification
- test40.elpi: functional output with pi quantification and premise
- test44.elpi: local clause with premise and same variable as the one received in input

### Failure

- test1.elpi: overlapping heads no bang rigid terms
- test3.elpi: non functional premise
- test5.elpi: local non functional clause
- test6.elpi: nested local non-functional clauses
- test7.elpi: local non-functional clauses
- test8.elpi: local non-functional clauses
- test9.elpi: local nested non-functional premises
- test10.elpi: local nested non-functional premises
- test11.elpi: overlapping heads using uvars
- test13.elpi: overlapping heads with two rules using the uvar keyword
- test14.elpi: non-functional variable used in variable used in the clause head
- test18.elpi: functional predicate with non functional argument
- test19.elpi: nested functional predicate with non functional argument
- test21.elpi: wrong-if: non-declared functional argument used in non functional ctx
- test23.elpi: similar to test14
- test24.elpi: ho output used in two different calls with different functionality relation
- test25.elpi: non functional ho output used to produce output of the rule
- test26.elpi: overlap with as operator
- test27.elpi: overlap with HO term in PF (B x) against (A x y)
- test30.elpi: non functional pred pass instead of functional, makes the premise non functional 
- test31.elpi: non functional output
- test33.elpi: non functional output in nested call
- test34.elpi: non functional output in nested call (use of map and lambda-abs)
- test35.elpi: non functional output in nested call (with non instantiated variable)
- test37.elpi: predicate with functional output + cut + call to the output
- test38.elpi: non functional output using pi constructor
- test41.elpi: non functional output with pi quantification and relational premise
- test42.elpi: local premise, with no guarantee on the functional output.
- test43.elpi: local clause use the same variable in the parent clause, no guarantee of the output