theorem not_xor (P Q : Prop) : ¬Xor P Q ↔ (P ↔ Q) := by
  constructor
  · intro h
    constructor
    · intro hp
      by_cases hq : Q
      · exact hq
        · exfalso
          apply h
          left
          exact ⟨hp, hq⟩
    · intro hq
      by_cases hp : P
      · exact hp
        · exfalso
          apply h
          right
          exact ⟨hp, hq⟩
  · intro h
    intro hXor
    cases hXor with
    | inl h1 =>
      rcases h1 with ⟨hp, hq⟩
      have : Q := (iff_iff_implies_and_implies.mp h).1 hp
      exact hq this
    | inr h2 =>
      rcases h2 with ⟨hp, hq⟩
      have : P := (iff_iff_implies_and_implies.mp h).2 hq
      exact hp this