theorem Xor.or {a b : Prop} (h : Xor a b) : a ∨ b := by
  cases h
  · left; exact h.1
  · right; exact h.2
