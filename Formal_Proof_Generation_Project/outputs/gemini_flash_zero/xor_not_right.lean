theorem xor_not_right {a b : Prop} : Xor a ¬b ↔ (a ↔ b) := by
  constructor
  · intro h
    cases h with
    | inl h1 =>
      constructor
      · intro _
        by_contra hb
        exact h1.right hb
      · intro _
        exact h1.left
    | inr h2 =>
      constructor
      · intro ha
        exact False.elim (h2.left ha)
      · intro hb
        exact False.elim (h2.right hb)
  · intro h
    by_cases ha : a
    · left
      constructor
      · exact ha
      · intro hnb
        exact hnb (h.mp ha)
    · right
      constructor
      · exact ha
      · intro hb
        exact ha (h.mpr hb)