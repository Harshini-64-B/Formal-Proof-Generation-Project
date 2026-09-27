theorem left_eq_add {M : Type u_4} [AddMonoid M] [IsLeftCancelAdd M] {a b : M} : a = a + b ↔ b = 0 := by
  constructor
  · intro h
    rw [add_zero a]
    exact (IsLeftCancelAdd.cancel a a b (by rw [add_zero a, h])).symm
  · intro h
    rw [h, add_zero a]