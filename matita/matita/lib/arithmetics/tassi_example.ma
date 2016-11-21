include "nat.ma".

(* example (Enrico Tassi) to test comptation performance of CIC kernels *)

lemma example_with_sharing:
let m ≝ 7 * 7 in
let n ≝ m * m in
S m - m = 1.
whd
letin m ≝ (7 * 7)
letin n ≝ (m * m)
@refl qed-.

(* FG and CSC kernels do not terminate, ET kernel does *)
lemma example_without_sharing: S ((7 * 7) * (7 * 7)) - ((7 * 7) * (7 * 7)) = 1.
@refl qed-.
