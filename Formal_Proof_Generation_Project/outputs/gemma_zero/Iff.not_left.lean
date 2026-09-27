theorem Iff.not_left {a b : Prop} (h : a ↔ ¬b) : ¬a ↔ b := by
  exact (Iff.not_iff.mpr h).trans (Iff.not_not b)