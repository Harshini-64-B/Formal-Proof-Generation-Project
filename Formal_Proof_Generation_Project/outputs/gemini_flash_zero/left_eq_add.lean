theorem left_eq_add {M : Type u_4} [AddMonoid M] [IsLeftCancelAdd M] {a b : M} : a = a + b ↔ b = 0 := by
  constructor
  · intro h
    have h1 : a + 0 = a + b := by rw [add_zero, h]
    exact (add_left_cancel h1).symm
  · rintro rfl
    rw [add_zero]