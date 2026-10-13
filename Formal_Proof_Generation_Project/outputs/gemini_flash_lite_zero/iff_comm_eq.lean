theorem exercise_2_2_3 {P Q R : Prop} : (P → Q → R) → (P → Q) → P → R := by
  intros h1 h2 h3
  exact h1 h3 (h2 h3)