theorem Peirce_law (P Q : Prop) : ((P → Q) → P) → P := by
  intro h
  by_cases hP : P
  · exact hP
  · exfalso
    apply h
    intro hp
    exfalso
    exact hP hp