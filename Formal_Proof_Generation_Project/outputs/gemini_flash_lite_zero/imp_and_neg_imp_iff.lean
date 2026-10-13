theorem modus_ponens (P Q : Prop) (h1 : P → Q) (h2 : P) : Q := by
  exact h1 h2