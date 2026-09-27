theorem iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) := by
  apply propext
  constructor
  · exact propext
  · intro h
    cases h
    exact Iff.rfl