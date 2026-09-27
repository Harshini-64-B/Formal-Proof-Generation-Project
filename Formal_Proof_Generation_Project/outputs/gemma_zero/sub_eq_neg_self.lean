theorem sub_eq_neg_self {G : Type u_3} [AddGroup G] {a b : G} : a - b = -b ↔ a = 0 := by
  constructor
  · intro h
    rw [sub_eq_add_neg] at h
    rw [add_right_assoc] at h
    rw [add_right_neg] at h
    rw [add_zero] at h
    exact h
  · intro h
    rw [h, sub_eq_add_neg]