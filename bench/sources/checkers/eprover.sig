sig eprover.

accum_sig resolution_steps.
accum_sig binary_res_fol_nosub.
accum_sig paramodulation.
accum_sig lists.
accum_sig certificatesLKF.

% constructor for rclause
type id index -> rclause.

% unary rules
type cn
 rclause -> int -> resolv.

type ignore_rule resolv -> o.
type unary_rule resolv -> int -> int -> o.
type param_rule resolv -> int -> int -> int -> o.

% binary rules
type pm,
     rw
 rclause -> rclause -> int -> resolv.

