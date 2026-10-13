theorem mul_eq_left {M : Type u_4} [Monoid M] [IsLeftCancelMul M] {a b : M} : a * b = a ↔ b = 1 := by
  constructor
  · intro h
    apply mul_left_cancel (a := a)
    simpa using h.symm
  · intro h
    simpa