theorem pow_sub_one {x a : ℕ} (hx : x ≠ 0) (ha : a ≠ 0) : x ^ (a - 1) = x ^ a / x := by
  cases a with
  | zero => contradiction
  | succ a =>
    simp [pow_succ, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hx)]