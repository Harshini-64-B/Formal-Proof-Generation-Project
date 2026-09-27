theorem sub_eq_neg_self {G : Type u_3} [AddGroup G] {a b : G} : a - b = -b ↔ a = 0 := by
  constructor
  · intro h
    have h1 : a - b + b = -b + b := by rw [h]
    rw [sub_add_cancel, neg_add_self] at h1
    exact h1
  · intro h
    rw [h, zero_sub]