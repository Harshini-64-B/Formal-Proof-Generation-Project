theorem eq_zero_iff_eq_zero_of_add_eq_zero {M : Type u_4} [AddZeroClass M] {a b : M} (h : a + b = 0) : a = 0 ↔ b = 0 := by
  constructor
  · intro ha
    rw [ha, zero_add] at h
    exact h
  · intro hb
    rw [hb, add_zero] at h
    exact h