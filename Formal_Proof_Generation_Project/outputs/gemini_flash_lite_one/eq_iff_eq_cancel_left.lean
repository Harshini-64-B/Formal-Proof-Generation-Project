theorem eq_iff_eq_cancel_left {b c : α} : (∀ {a}, a = b ↔ a = c) ↔ b = c := by
  constructor
  · intro h
    have h1 : b = b ↔ b = c := h
    exact h1.mp rfl
  · intro h a
    subst h
    constructor <;> intro h_1 <;> exact h_1