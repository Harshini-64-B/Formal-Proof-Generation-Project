theorem left_eq_add {M : Type u_4} [AddMonoid M] [IsLeftCancelAdd M] {a b : M} : a = a + b ↔ b = 0 := by
  constructor
  · intro h
    have h2 : a + 0 = a + b := by
      rw [add_zero, ← h]
    exact add_left_cancel h2
  · intro h
    rw [h, add_zero]