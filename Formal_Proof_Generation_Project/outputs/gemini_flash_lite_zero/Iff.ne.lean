theorem Iff.ne {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c = d) → (a ≠ b ↔ c ≠ d) := by
  intro h
  constructor
  · intro h1 h2
    apply h1
    exact (iff_iff_eq_eq_or_something... wait, use not_iff)
    exact (iff_not_iff.mp h).mp h2
  · intro h1 h2
    apply h1
    exact (iff_not_iff.mp h).mpr h2