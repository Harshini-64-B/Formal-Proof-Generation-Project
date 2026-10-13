theorem xor_not_right {a b : Prop} : Xor a ¬b ↔ (a ↔ b) := by
  constructor
  · rintro (⟨ha, hnb⟩ | ⟨hna, hb⟩)
    · constructor
      · intro h
        exact ha
      · intro h
        by_contra hnb'
        exact hnb hnb'
    · constructor
      · intro ha'
        exfalso
        exact hna ha'
      · intro hb'
        exact hb
  · intro h
    rcases h with ⟨hab1, hab2⟩
    by_cases ha : a
    · left
      refine ⟨ha, ?_⟩
      intro hnb
      exact hnb (hab1 ha)
    · right
      refine ⟨ha, ?_⟩
      intro hb
      exact ha (hab2 hb)