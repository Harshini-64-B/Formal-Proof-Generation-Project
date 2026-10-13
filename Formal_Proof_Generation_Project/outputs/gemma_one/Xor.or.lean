theorem Xor.or {a b : Prop} (h : Xor a b) : a ∨ b := by
  exact h.1