theorem xor_not_not {a b : Prop} : Xor (¬a) ¬b ↔ Xor a b := by
  unfold Xor
  tauto