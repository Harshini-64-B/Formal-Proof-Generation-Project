theorem mul_inv_cancel_left {G : Type*} [Group G] (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, mul_left_inv, one_mul]