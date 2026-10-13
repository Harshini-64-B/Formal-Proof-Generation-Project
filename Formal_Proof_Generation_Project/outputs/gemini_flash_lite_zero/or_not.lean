theorem exercise_3_1_1 {P Q R : Prop} : (P → Q → R) → (P → Q) → P → R := by
  intros h1 h2 h3
  exact h1 h3 (h2 h3)