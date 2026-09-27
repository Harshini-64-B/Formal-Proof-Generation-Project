theorem add_add_add_comm {G : Type u_3} [AddCommSemigroup G] (a b c d : G) : a + b + (c + d) = a + c + (b + d) := by
  simp [add_assoc, add_comm]