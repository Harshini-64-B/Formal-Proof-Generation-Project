theorem ne_and_eq_iff_right {a b c : α} (h : b ≠ c) : a ≠ b ∧ a = c ↔ a = c := by
  constructor
  · intro h1
    exact h1.right
  · intro h1
    constructor
    · intro h2
      subst h1
      exact h h2.symm
    · exact h1