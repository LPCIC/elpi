sig resolution_steps.

accum_sig certificatesLKF.
accum_sig lists.
accum_sig res_base.
accum_sig base.

kind rstep type.
kind resolv type.
kind rclause type.
kind state type. % additional information which might be required by implementing fpcs.

type estate state. %empty state
type istate list int -> state. %state of input formula operands indices

type resolv rclause -> rclause -> int -> resolv.
type rsteps list resolv -> state -> cert. % sequence of steps and a state
type resteps list resolv -> cert. % sequence of steps

type dlist rclause -> rclause -> cert.

