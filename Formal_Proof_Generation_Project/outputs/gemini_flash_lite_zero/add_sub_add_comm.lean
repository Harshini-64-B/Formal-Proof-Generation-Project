theorem add_sub_add_comm {α : Type u_1} [SubtractionCommMonoid α] (a b c d : α) : a + b - (c + d) = a - c + (b - d) := by
  exact add_sub_add_comm a b c d