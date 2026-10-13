theorem and_symm_right {α : Sort u_1} (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a := by
  constructor
  · intro h
    rcases h with ⟨hp, hab⟩
    exact ⟨hp, hab.symm⟩
  · intro h
    rcases h with ⟨hp, hba⟩
    exact ⟨hp, hba.symm⟩