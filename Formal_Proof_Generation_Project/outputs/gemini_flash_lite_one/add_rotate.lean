theorem add_rotate {G : Type u_3} [AddCommSemigroup G] (a b c : G) : a + b + c = b + c + a := by
  rw [add_assoc, add_comm a, ← add_assoc]