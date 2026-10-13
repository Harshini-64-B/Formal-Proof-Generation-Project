theorem group_self_inverse {G : Type*} [Group G] {a : G} (h : a * a = 1) : a⁻¹ = a := by
  have h1 : a⁻¹ * (a * a) = a⁻¹ * 1 := by rw [h]
  rw [mul_one] at h1
  rw [← mul_assoc, inv_mul_cancel, one_mul] at h1
  exact h1.symm