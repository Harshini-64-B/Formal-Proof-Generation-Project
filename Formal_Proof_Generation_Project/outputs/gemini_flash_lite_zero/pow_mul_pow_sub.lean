theorem mul_self_eq_one_iff {G : Type*} [Group G] {x : G} : x * x = 1 ↔ x = x⁻¹ := by
  constructor
  · intro h
    rw [← h, mul_inv_cancel_right]
  · intro h
    rw [h, mul_inv_cancel]