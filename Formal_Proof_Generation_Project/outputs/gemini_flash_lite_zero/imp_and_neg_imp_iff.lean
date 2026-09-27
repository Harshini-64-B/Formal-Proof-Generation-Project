theorem imp_and_neg_imp_iff (p q : Prop) : (p → q) ∧ (¬p → q) ↔ q := by
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hp : p
    · exact h1 hp
    · exact h2 hp
  · intro hq
    exact ⟨fun _ => hq, fun _ => hq⟩