theorem inv_eq_of_mul_eq_one {G : Type*} [Group G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  have h1 : a⁻¹ * (a * b) = a⁻¹ * 1 := by rw [h]
  rw [mul_one, ← mul_assoc, inv_mul_cancel, one_mul] at h1
  exact h1.symm