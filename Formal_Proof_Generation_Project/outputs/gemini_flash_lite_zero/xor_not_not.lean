theorem exercise_3_1_8 {P Q R : Prop} : (P → Q ∧ R) → (P → Q) := by
  intro h p
  have hqr := h p
  exact hqr.left