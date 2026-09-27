theorem and_symm_right {α : Sort u_1} (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a := by
  constructor
  · rintro ⟨hp, rfl⟩
    exact ⟨hp, rfl⟩
  · rintro ⟨hp, rfl⟩
    exact ⟨hp, rfl⟩