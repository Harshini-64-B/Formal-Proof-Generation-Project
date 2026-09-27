theorem pow_sub_one {x a : ℕ} (hx : x ≠ 0) (ha : a ≠ 0) : x ^ (a - 1) = x ^ a / x := by
  rw [← Nat.sub_add_cancel ha, Nat.pow_mul (a - 1) 1, Nat.pow_one x, Nat.div_mul_cancel hx]