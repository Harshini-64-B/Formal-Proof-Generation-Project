theorem mul_eq_left {M : Type u_4} [Monoid M] [IsLeftCancelMul M] {a b : M} : a * b = a ↔ b = 1 := by
  constructor
  · intro h
    rw [mul_one a] at h
    exact mul_left_cancel h
  · intro h
    rw [h, mul_one a]