theorem distrib_and_or (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · rintro ⟨p, q | r⟩
    · left; exact ⟨p, q⟩
    · right; exact ⟨p, r⟩
  · rintro (⟨p, q⟩ | ⟨p, r⟩)
    · exact ⟨p, Or.inl q⟩
    · exact ⟨p, Or.inr r⟩