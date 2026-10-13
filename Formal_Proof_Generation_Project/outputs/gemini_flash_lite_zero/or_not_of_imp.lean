theorem exercise_1_1_4 {P Q R : Prop} : ((P → Q) ∧ (Q → R)) → (P → R) := by
  intro h p
  rcases h with ⟨h1, h2⟩
  exact h2 (h1 p)