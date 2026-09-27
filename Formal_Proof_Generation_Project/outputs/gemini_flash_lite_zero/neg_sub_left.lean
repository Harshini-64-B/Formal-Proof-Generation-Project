theorem neg_sub_left {α : Type u_1} [SubtractionMonoid α] (a b : α) : -a - b = -(b + a) := by
  rw [sub_eq_neg_add, neg_add_rev, add_comm]