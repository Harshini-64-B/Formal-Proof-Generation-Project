theorem xor_not_left {a b : Prop} : Xor (¬a) b ↔ (a ↔ b) := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨fun ha => absurd ha h1, fun hb => absurd hb h2⟩
    · exact ⟨fun _ => h2, fun _ => by tauto⟩
  · intro hab
    by_cases ha : a
    · right
      exact ⟨ha, hab.mp ha⟩
    · left
      exact ⟨ha, fun hb => ha (hab.mpr hb)⟩