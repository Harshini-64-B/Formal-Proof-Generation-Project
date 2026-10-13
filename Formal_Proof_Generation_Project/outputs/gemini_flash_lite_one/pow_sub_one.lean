theorem pow_sub_one {x a : ℕ} (hx : x ≠ 0) (ha : a ≠ 0) : x ^ (a - 1) = x ^ a / x := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  rw [Nat.add_sub_cancel, pow_succ, Nat.mul_div_cancel_left _ hx]