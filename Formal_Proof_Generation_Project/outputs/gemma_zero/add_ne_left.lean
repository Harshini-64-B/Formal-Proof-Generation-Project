theorem add_ne_left {M : Type u_4} [AddMonoid M] [IsLeftCancelAdd M] {a b : M} : a + b ≠ a ↔ b ≠ 0 := by
  rw [← ne_eq, ← ne_eq]
  constructor
  · intro h
    rw [← add_zero]
    exact add_left_cancel a b 0
  · intro h
    rw [h, add_zero]