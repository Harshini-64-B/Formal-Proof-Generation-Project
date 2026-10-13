theorem not_xor (P Q : Prop) : ¬Xor P Q ↔ (P ↔ Q) := by
  unfold Xor
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
          exact ⟨hq, hp⟩
  · intro h
    intro h_xor
    rcases h_xor with ⟨hp, hq⟩ | ⟨hq, hp⟩
    · exact hq (h.mp hp)
    · exact hp (h.mpr hq)