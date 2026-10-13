theorem xor_not_right {a b : Prop} : Xor a ¬b ↔ (a ↔ b) := by
  constructor
  · intro h
    simp [Xor] at h
    simp at h
    exact h
  · intro h
    simp [Xor]
    simp at h
    exact h