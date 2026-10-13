theorem left_eq_add {M : Type u_4} [AddMonoid M] [IsLeftCancelAdd M] {a b : M} : a = a + b ↔ b = 0 := by
  constructor
  · intro h
    apply add_left_cancel (a := a)
    simpa using h.symm
  · intro h
    simpa [h]