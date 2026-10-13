theorem de_morgan_not_and_not (P Q : Prop) : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      exact h ⟨hP, hQ⟩
    · left
      exact hP
  · intro h hpq
    rcases h with hp | hq
    · exact hp hpq.1
    · exact hq hpq.2