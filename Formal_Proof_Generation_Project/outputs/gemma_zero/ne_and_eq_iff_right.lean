theorem ne_and_eq_iff_right {a b c : α} (h : b ≠ c) : a ≠ b ∧ a = c ↔ a = c := by
  constructor
  · intro h_and
    exact h_and.right
  · intro h_eq
    constructor
    · intro h_eq_ab
      rw [h_eq] at h_eq_ab
      exact h h_eq_ab.symm
    · exact h_eq