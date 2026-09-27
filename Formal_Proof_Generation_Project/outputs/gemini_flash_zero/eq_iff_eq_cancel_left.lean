theorem eq_iff_eq_cancel_left {b c : α} : (∀ {a}, a = b ↔ a = c) ↔ b = c := by
  constructor
  · intro h
    exact h.mp rfl
  · intro h
    cases h
    intro a
    rfl