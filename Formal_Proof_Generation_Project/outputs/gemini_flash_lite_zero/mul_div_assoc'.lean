theorem group_cancel_left {G : Type*} [Group G] (a b c : G) (h : a * b = a * c) : b = c := by
  have h1 : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by rw [h]
  rw [← mul_assoc, inv_mul_cancel, one_mul] at h1
  rw [← mul_assoc, inv_mul_cancel, one_mul] at h1
  exact h1