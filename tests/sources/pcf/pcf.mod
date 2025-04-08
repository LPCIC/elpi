/* combines script1 to script4.
 */

module pcf.


accumulate eval_test, mono_test, poly_test, tr_test, examples.

type main o.

main :- % std.spy(eval_test 1 V1), !,
        % std.spy(eval_test 2 V2), !,
        % std.spy(eval_test 3 V3), !,
        % V1 = in 144, 
        % V2 = (lcons # in 2 # (lcons # in 8 # empty)),
        % V3 = (lcons # in 3 # (lcons # in 5 # empty)),
        std.spy(mono_test "onep" Ty1), !,
        std.spy(mono_test "is_sym" Ty2), !,
        std.spy(mono_test "fib" Ty3), !,
        std.spy(poly_test "successor" Ty4), !,
        std.spy(poly_test "onep" Ty5), !,
        std.spy(poly_test "is_sym" Ty6), !,
        std.spy(tr_test "successor"), !,
        std.spy(tr_test "onep"), !,
        std.spy(tr_test "is_sym").
