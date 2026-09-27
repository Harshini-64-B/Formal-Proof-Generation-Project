theorem not_xor (P Q : Prop) : ¬Xor P Q ↔ (P ↔ Q) := by
  constructor
  · intro h
    rw [Xor] at h
    simp [h]
  · intro h
    rw [Xor]
    intro h
    simp [h] at h
    exact h.elim