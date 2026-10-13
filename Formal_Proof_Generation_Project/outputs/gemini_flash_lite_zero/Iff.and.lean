theorem Peirce (P Q : Prop) : ((P → Q) → P) → P := by
  intro h
  by_cases hP : P
  · exact hP
  · exfalso
    apply h
    intro p
    exfalso
    exact hP p