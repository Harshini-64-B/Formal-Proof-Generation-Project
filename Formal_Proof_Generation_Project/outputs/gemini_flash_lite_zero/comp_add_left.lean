theorem inv_unique {G : Type*} [Group G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  calc a⁻¹ = a⁻¹ * 1 := (mul_one a⁻¹).symm
  _ = a⁻¹ * (a * b) := by rw [h]
  _ = (a⁻¹ * a) * b := (mul_assoc a⁻¹ a b).symm
  _ = 1 * b := by rw [inv_mul_cancel]
  _ = b := one_mul b