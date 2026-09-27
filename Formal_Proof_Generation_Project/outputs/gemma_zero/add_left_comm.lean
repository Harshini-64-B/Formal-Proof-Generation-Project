theorem add_left_comm {G : Type u_3} [AddCommSemigroup G] (a b c : G) : a + (b + c) = b + (a + c) := by
  simp [add_assoc, add_comm]