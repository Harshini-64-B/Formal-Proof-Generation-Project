theorem inv_unique {G : Type*} [Group G] {x y : G} (h : x * y = 1) : x⁻¹ = y := by
  have h1 : x⁻¹ * (x * y) = x⁻¹ * 1 := by rw [h]
  rw [mul_one, ← mul_assoc, inv_mul_cancel, one_mul] at h1
  exact h1.symm