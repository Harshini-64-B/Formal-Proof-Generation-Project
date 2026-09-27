theorem eq_one_iff_eq_one_of_mul_eq_one {M : Type u_4} [MulOneClass M] {a b : M} (h : a * b = 1) :a = 1 ↔ b = 1 := by
  constructor
  · intro ha
    rw [ha, one_mul] at h
    exact h
  · intro hb
    rw [hb, mul_one] at h
    exact h