theorem group_inv_unique {G : Type*} [Group G] {a b : G} (h : a * b = 1) : b = a⁻¹ := by
  calc
    b = 1 * b := (one_mul b).symm
    _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * b) := (mul_assoc a⁻¹ a b).symm
    _ = a⁻¹ * 1 := by rw [h]
    _ = a⁻¹ := mul_one a⁻¹