theorem not_xor (P Q : Prop) : ¬Xor P Q ↔ (P ↔ Q) := by
  constructor
  · intro h
    constructor
    · intro hP
      intro hQ
      exfalso
      have h_and : P ∧ Q := ⟨hP, hQ⟩
      have h_or : P ∨ Q := Or.inl hP
      have h_not_and : ¬(P ∧ Q) := fun h => h h_and
      exact h ⟨h_or, h_not_and⟩
    · intro hQ
      intro hP
      exfalso
      have h_and : P ∧ Q := ⟨hP, hQ⟩
      have h_or : P ∨ Q := Or.inr hQ
      have h_not_and : ¬(P ∧ Q) := fun h => h h_and
      exact h ⟨h_or, h_not_and⟩
  · intro h
    intro hX
    simp [Xor] at hX
    rcases hX with ⟨h_or, h_not_and⟩
    cases h_or with
    | inl hP =>
      have hQ : Q := h.mp hP
      exact h_not_and (And.intro hP hQ)
    | inr hQ =>
      have hP : P := h.mpr hQ
      exact h_not_and (And.intro hP hQ)