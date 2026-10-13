theorem not_ne_iff {α : Sort u_1} {a b : α} : ¬a ≠ b ↔ a = b := by
  constructor
  · intro h
    exact Classical.not_not h
  · intro h
    intro h_ne
    exact h_ne h