theorem xor_not_left {a b : Prop} : Xor (¬a) b ↔ (a ↔ b) := by
  unfold Xor
  constructor
  · intro h
    cases h with
    | inl h1 =>
      cases h1 with
      | intro hna hnb =>
        constructor
        · intro ha; contradiction
        · intro hb; contradiction
    | inr h2 =>
      cases h2 with
      | intro hh hb =>
        constructor
        · intro _; exact hb
        · intro _; by_contra hna; exact hh hna
  · intro h
    by_cases ha : a
    · right
      constructor
      · intro hna; exact hna ha
      · exact h.mp ha
    · left
      constructor
      · exact ha
      · intro hb; exact ha (h.mpr hb)