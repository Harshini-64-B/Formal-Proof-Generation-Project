theorem group_inv_unique {G : Type*} [Group G] {a b : G} (h : a * b = 1) : b = a⁻¹ := by
  have h1 : a⁻¹ * (a * b) = a⁻¹ * 1 := by rw [h]
  rw [mul_assoc, inv_mul_cancel, one_mul, mul_one] at h1
  exact h1.symm