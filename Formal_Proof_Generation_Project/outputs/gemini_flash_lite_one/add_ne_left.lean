theorem add_ne_left {M : Type u_4} [AddMonoid M] [IsLeftCancelAdd M] {a b : M} : a + b ≠ a ↔ b ≠ 0 := by
  constructor
  · intro h hb
    apply h
    rw [hb, add_zero]
  · intro h he
    apply h
    have : a + b = a + 0 := by
      rw [he, add_zero]
    exact add_left_cancel this