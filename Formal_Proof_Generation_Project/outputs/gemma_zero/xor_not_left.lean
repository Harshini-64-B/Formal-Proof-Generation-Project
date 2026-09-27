theorem xor_not_left {a b : Prop} : Xor (¬a) b ↔ (a ↔ b) := by
  rw [Xor, not_iff_not]