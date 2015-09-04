module logic.

accumulate hcinterp_examples.
accumulate hcsyntax_examples.
accumulate pnf_examples.

only_three :- not (pathfroma X, not (X = b), not (X = c), not (X = (f c))).

main :- pathfroma X,
        pathfroma b,
        pathfroma c,
        pathfroma (f c),
        only_three,
        test_goal 1,
        test_goal 3,
        test_defcl 4,
        test_defcl 5,
        test_defcl 6,
        test 1 F1, F1 = some (x\ path a x imp tru), 
        test 2 F2, F2 = all (x\ path a x imp tru),
        test 3 F3, F3 = all (x\ path a x and path x a),
        test 3 F31, F31 = all (x\ all (y\ path a x and path y a)),
        test 3 F32, F32 = all (x\ all (y\ path a y and path x a)),
        test 4 F4, F4 = all (x\ all (y\ path a x imp path a y)),
        test 4 F5, F5 = all (x\ all (y\ path a y imp path a x)).



