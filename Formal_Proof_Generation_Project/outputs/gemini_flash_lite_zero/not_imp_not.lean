theorem demorgans_law_1 {P Q : Prop} : ¬ (P ∨ Q) → ¬ P ∧ ¬ Q := by
  intro h
  constructor
  · intro hp
    apply h
    left
    exact hp
  · intro hq
    apply h
    right
    exact hq