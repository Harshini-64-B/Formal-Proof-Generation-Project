def Xor (a b : Prop) : Prop := (a ∧ ¬b) ∨ (¬a ∧ b)

theorem xor_not_not {a b : Prop} : Xor (¬a) ¬b ↔ Xor a b := by
  unfold Xor
  simp [not_not, or_comm]