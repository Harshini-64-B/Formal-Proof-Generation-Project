theorem add_ne_left {M : Type u_4} [AddMonoid M] [IsLeftCancelAdd M] {a b : M} : a + b ≠ a ↔ b ≠ 0 := by
  constructor
  · intro h
    intro h0
    have h_eq : a + b = a := by rw [← h0, add_zero]
    exact h h_eq
  · intro h
    intro h_eq
    have h_b0 : b = 0 := by
      apply add_left_cancel (a := a)
      rw [h_eq, add_zero]
    exact h h_b0