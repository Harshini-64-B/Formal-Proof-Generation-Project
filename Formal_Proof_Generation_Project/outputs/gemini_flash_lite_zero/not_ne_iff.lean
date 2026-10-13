theorem exercise_1_1_4 (P Q R : Prop) : (P → (Q → R)) → ((P → Q) → (P → R)) := by
  intro h1 h2 h3
  exact h1 h3 (h2 h3)