theorem left_inv_eq_right_inv {G : Type*} [Group G] {x y z : G} (h1 : x * y = 1) (h2 : z * x = 1) : y = z := by
  have h3 : z * (x * y) = z * 1 := by rw [h1]
  rw [mul_one] at h3
  rw [← mul_assoc] at h3
  rw [h2] at h3
  rw [one_mul] at h3
  exact h3.symm