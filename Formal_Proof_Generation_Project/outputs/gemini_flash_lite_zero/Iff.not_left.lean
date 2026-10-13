theorem ex_1_3_7 (P Q : Prop) : (P ∧ Q) ∨ (P ∧ ¬Q) ↔ P := by
  constructor
  · rintro (⟨hP, _⟩ | ⟨hP, _⟩)
    · exact hP
    · exact hP
  · intro hP
    by_cases hQ : Q
    · left
      exact ⟨hP, hQ⟩
    · right
      exact ⟨hP, hQ⟩