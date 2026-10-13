theorem demorgan_1 {P Q : Prop} : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  intro h
  constructor
  · intro p
    apply h
    left
    exact p
  · intro q
    apply h
    right
    exact q