theorem neg_sub_left {α : Type u_1} [SubtractionMonoid α] (a b : α) : -a - b = -(b + a) := by
  rw [neg_add_rev]