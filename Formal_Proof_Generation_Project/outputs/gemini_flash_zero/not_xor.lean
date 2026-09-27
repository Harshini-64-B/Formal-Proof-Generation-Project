theorem not_xor (P Q : Prop) : ¬Xor P Q ↔ (P ↔ Q) := by
  constructor
  · intro h
    constructor
    · intro hP
      by_cases hQ : Q
      · exact hQ
      · exfalso
        apply h
        left
        exact ⟨hP, hQ⟩
    · intro hQ
      by_cases hP : P
      · exact hP
      · exfalso
        apply h
        right
        exact ⟨hP, hQ⟩
  · intro h hXor
    cases hXor with
    | inl h1 =>
      exact h1.right (h.mp h1.left)
    | inr h2 =>
      exact h2.left (h.mpr h2.right)