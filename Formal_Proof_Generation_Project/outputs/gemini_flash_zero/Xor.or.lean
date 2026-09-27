theorem Xor.or {a b : Prop} (h : Xor a b) : a ∨ b := by
  cases h with
  | inl h => exact Or.inl h.left
  | inr h => exact Or.inr h.right