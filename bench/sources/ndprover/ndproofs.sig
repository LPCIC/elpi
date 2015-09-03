/*
 * Encodings of proofs in the natural deduction calculus
 */

sig  ndproofs.

accum_sig  logic.

kind    proof_object	type.

type    and_i           proof_object -> proof_object -> proof_object.
type    or_i1           proof_object -> proof_object.
type    or_i2           proof_object -> proof_object.
type    imp_i           (proof_object -> proof_object) -> proof_object.
type    forall_i        (i -> proof_object) -> proof_object.
type    exists_i        i -> proof_object -> proof_object.
type    and_e1          proof_object -> proof_object.
type    and_e2          proof_object -> proof_object.
type    imp_e           proof_object -> proof_object -> proof_object.
type    forall_e        i -> proof_object -> proof_object.
type    or_e            proof_object -> (proof_object -> proof_object) ->
                         (proof_object -> proof_object) -> proof_object.
type    exists_e        proof_object ->
                         (i -> proof_object -> proof_object) ->
                         proof_object.

