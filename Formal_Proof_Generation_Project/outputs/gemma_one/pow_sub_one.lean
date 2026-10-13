theorem pow_sub_one {x a : ℕ} (hx : x ≠ 0) (ha : a ≠ 0) : x ^ (a - 1) = x ^ a / x := by
  have h_eq : a = (a - 1) + 1 := Nat.sub_add_one_eq_self ha
  rw [← h_eq, Nat.pow_succ x (a - 1)]
  exact Nat.div_eq_of_mul_eq_of_ne_zero (by rfl) hx