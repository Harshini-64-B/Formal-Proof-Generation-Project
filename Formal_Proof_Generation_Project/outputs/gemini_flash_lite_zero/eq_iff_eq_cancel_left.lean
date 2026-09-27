theorem eq_iff_eq_cancel_left {b c : α} : (∀ {a}, a = b ↔ a = c) ↔ b = c := by
  constructor
  · intro h
    exact (h.mp rfl).symm
  · intro h a
    rw [h]