theorem xor_not_right {a b : Prop} : Xor a ¬b ↔ (a ↔ b) := by
  unfold Xor
  constructor
  · rintro (⟨ha, hnb⟩ | ⟨hna, hb⟩)
    · exact ⟨ha, by tauto⟩
    · exact ⟨by tauto, hb⟩
  · rintro ⟨ha, hb⟩
    by_cases ha_prop : a
    · left
      exact ⟨ha_prop, by rw [ha_prop] at hb; exact hb⟩
    · right
      exact ⟨ha_prop, by rw [not_iff_not] at hb; exact hb ha_prop⟩