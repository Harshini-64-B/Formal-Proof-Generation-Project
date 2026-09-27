theorem mul_eq_left {M : Type u_4} [Monoid M] [IsLeftCancelMul M] {a b : M} : a * b = a ↔ b = 1 := by
  constructor
  · intro h
    have h1 : a * b = a * 1 := by rw [h, mul_one]
    exact mul_left_cancel h1
  · intro h
    rw [h, mul_one]