theorem Iff.not {a b : Prop} (h : a ↔ b) : ¬a ↔ ¬b := by
  exact ⟨fun ha hb => ha (h.mpr hb), fun hb ha => hb (h.mp ha)⟩