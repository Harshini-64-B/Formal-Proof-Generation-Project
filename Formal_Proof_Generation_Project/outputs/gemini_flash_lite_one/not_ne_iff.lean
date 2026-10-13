theorem not_ne_iff {α : Sort u_1} {a b : α} : ¬a ≠ b ↔ a = b := by
  constructor
  · intro h
    by_contra hab
    exact h hab
  · intro h
    intro hab
    exact hab h