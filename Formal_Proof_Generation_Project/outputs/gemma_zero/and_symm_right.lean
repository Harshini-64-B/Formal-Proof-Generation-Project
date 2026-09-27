theorem and_symm_right {α : Sort u_1} (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a := by
  constructor
  · intro ⟨hp, ha⟩
    exact ⟨hp, ha.symm⟩
  · intro ⟨hp, hb⟩
    exact ⟨hp, hb.symm⟩