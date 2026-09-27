theorem eq_iff_eq_cancel_left {α : Type} {b c : α} : (∀ {a}, a = b ↔ a = c) ↔ b = c := by
  constructor
  · intro h
    exact (h b).mp rfl
  · intro h
    intro a
    simp [h]