theorem neg_sub_left {α : Type u_1} [SubtractionMonoid α] (a b : α) : -a - b = -(b + a) := by
  rw [sub_eq_add_neg, ← neg_add]