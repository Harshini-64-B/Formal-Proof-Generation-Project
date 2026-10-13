theorem problem_1 (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  exact h2 (h1 h3)