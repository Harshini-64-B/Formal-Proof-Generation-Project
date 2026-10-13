theorem eq_zero_iff_eq_zero_of_add_eq_zero {M : Type u_4} [AddZeroClass M] {a b : M} (h : a + b = 0) : a = 0 ↔ b = 0 := by
  constructor
  · intro h_a
    rw [h_a] at h
    rw [zero_add] at h
    exact h
  · intro h_b
    rw [h_b] at h
    rw [add_zero] at h
    exact h