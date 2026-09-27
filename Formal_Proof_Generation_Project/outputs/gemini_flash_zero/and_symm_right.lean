theorem and_symm_right {α : Sort u_1} (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a :=
  ⟨fun ⟨hp, h⟩ => ⟨hp, h.symm⟩, fun ⟨hp, h⟩ => ⟨hp, h.symm⟩⟩