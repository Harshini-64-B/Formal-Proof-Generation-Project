theorem distributivity_and_or (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · rintro ⟨hP, hQR | hR⟩
    · left; exact ⟨hP, hQR⟩
    · right; exact ⟨hP, hR⟩
  · rintro (⟨hP, hQ⟩ | ⟨hP, hR⟩)
    · exact ⟨hP, Or.inl hQ⟩
    · exact ⟨hP, Or.inr hR⟩