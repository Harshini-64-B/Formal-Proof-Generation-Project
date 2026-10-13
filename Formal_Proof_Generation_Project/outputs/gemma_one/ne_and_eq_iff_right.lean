theorem ne_and_eq_iff_right {a b c : α} (h : b ≠ c) : a ≠ b ∧ a = c ↔ a = c := by
  constructor
  . intro h
    exact h.2
  . intro h_ac
    constructor
    . intro h_ab
      intro h_eq
      rw [h_eq] at h_ac
      exact h h_ac
    . exact h_ac