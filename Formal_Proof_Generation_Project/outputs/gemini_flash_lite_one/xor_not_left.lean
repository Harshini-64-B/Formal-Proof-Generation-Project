theorem xor_not_left {a b : Prop} : Xor (¬a) b ↔ (a ↔ b) := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · constructor
      · intro ha
        exfalso
        exact h1 ha
      · intro hb
        exfalso
        exact h2 hb
    · constructor
      · intro ha
        by_contra hnb
        exact h1 hnb
      · intro hb
        exact h2
  · intro h
    constructor
    · intro hna
      right
      constructor
      · exact hna
      · rw [← h]
        exact hna
    · intro hb
      left
      constructor
      · intro ha
        have : b := by
          rw [← h]
          exact ha
        exact hb this
      · exact hb