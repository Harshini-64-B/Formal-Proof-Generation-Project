theorem sub_eq_neg_self {G : Type u_3} [AddGroup G] {a b : G} : a - b = -b ↔ a = 0 := by
  rw [sub_eq_iff_eq_add, neg_add_cancel]