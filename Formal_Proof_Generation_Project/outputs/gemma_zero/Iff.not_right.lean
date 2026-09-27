theorem Iff.not_right {a b : Prop} (h : ¬a ↔ b) : a ↔ ¬b := by
  rw [not_iff_not] at h
  rw [not_not] at h
  exact h