theorem and_symm_right {α : Sort u_1} (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a := by
  constructor
  · intro h; exact ⟨h.left, h.right.symm⟩
  · intro h; exact ⟨h.left, h.right.symm⟩