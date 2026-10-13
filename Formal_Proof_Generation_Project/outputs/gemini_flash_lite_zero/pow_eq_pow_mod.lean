theorem mul_inv_eq_of_eq_mul {G : Type*} [Group G] {a b c : G} (h : a = c * b) : a * b⁻¹ = c := by
  rw [h, mul_inv_cancel_right]