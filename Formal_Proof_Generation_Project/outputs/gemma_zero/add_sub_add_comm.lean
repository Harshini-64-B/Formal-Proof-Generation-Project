theorem add_sub_add_comm {α : Type u_1} [SubtractionCommMonoid α] (a b c d : α) : a + b - (c + d) = a - c + (b - d) := by
  rw [sub_add, add_comm, add_sub, add_comm]