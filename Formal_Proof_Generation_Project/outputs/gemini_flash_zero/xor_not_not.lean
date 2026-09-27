theorem xor_not_not {a b : Prop} : Xor (¬a) ¬b ↔ Xor a b := by
  by_cases ha : a <;> by_cases hb : b <;> simp [Xor, ha, hb]