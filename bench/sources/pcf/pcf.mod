/* combines script1 to script4.
 */

module pcf.


accumulate eval_test, mono_test, poly_test, tr_test, examples.

type main o.

main :- eval_test 1 V1, 
        eval_test 2 V2,
        eval_test 3 V3,
        eval_test 3 V4,
        V1 = in 144, 
        V2 = (cons @ in 2 @ (cons @ in 8 @ empty)),
        V3 = (cons @ in 3 @ (cons @ in 5 @ empty)),
        V = truth,
        mono_test "onep" Ty1,
        mono_test "is_sym" Ty2,
        mono_test "fib" Ty3,
        poly_test "successor" Ty4,
        poly_test "onep" Ty5,
        poly_test "is_sym" Ty6,
        tr_test "successor",
        tr_test "onep",
        tr_test "is_sym".
