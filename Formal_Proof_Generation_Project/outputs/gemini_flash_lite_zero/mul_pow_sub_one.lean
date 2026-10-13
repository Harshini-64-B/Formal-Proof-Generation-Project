theorem group_inv_unique {G : Type*} [Group G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  calc a⁻¹ = a⁻¹ * (a * b) := by rw [h, mul_one]
       _ = (a⁻¹ * a) * b := by rw [mul_assoc]
       _ = 1 * b := by rw [inv_mul_cancel]
       _ = b := by rw [one_mul]