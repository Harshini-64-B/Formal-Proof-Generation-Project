theorem sub_eq_neg_self {G : Type u_3} [AddGroup G] {a b : G} : a - b = -b ↔ a = 0 := by
  constructor
  · intro h
    rw [sub_eq_add_neg] at h
    rw [add_left_id] at h
    exact add_right_cancel h
  · intro h
    rw [h, sub_eq_add_neg, add_left_id]