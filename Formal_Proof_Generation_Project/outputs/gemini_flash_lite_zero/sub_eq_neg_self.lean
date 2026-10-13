theorem group_left_inverse {G : Type*} [Group G] (a : G) : a⁻¹ * a = 1 := by
  exact mul_left_inv a