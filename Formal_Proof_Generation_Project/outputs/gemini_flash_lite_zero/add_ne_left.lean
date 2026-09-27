theorem add_ne_left {M : Type u_4} [AddMonoid M] [IsLeftCancelAdd M] {a b : M} : a + b ≠ a ↔ b ≠ 0 := by
  constructor
  · intro h hb
    apply h
    rw [hb, add_zero]
  · intro h hab
    apply h
    exact add_left_cancel hab