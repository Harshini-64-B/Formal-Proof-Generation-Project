theorem add_ne_left {M : Type u_4} [AddMonoid M] [IsLeftCancelAdd M] {a b : M} : a + b ≠ a ↔ b ≠ 0 := by
  simp only [ne_eq, add_left_eq_self]