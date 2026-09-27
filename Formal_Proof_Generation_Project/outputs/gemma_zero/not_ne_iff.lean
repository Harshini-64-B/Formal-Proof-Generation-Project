theorem not_ne_iff {α : Sort u_1} {a b : α} : ¬a ≠ b ↔ a = b := by
  constructor
  · intro h
    exact h.not_not
  · intro h
    intro h_ne
    contradiction