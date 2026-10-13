theorem problem_1 (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  intros h1 h2 hp
  apply h2
  apply h1
  exact hp