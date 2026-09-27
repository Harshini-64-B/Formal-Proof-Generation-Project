theorem add_sub_add_comm {α : Type u_1} [SubtractionCommMonoid α] (a b c d : α) : a + b - (c + d) = a - c + (b - d) := by
  rw [sub_add_eq_sub_sub, add_sub_right_comm, add_sub_assoc]