theorem xor_not_not {a b : Prop} : Xor (¬a) ¬b ↔ Xor a b := by
  simp [Xor]