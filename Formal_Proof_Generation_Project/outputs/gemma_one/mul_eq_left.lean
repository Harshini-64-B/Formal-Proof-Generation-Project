theorem mul_eq_left {M : Type u_4} [Monoid M] [IsLeftCancelMul M] {a b : M} : a * b = a ↔ b = 1 := by
  constructor
  · intro h
    rw [← mul_one a] at h
    exact left_cancel (a := a) h
  · intro h
    rw [h]
    exact mul_one a