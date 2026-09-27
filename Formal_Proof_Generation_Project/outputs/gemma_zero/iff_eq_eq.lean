theorem iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) := by
  apply propext
  constructor
  · intro h
    exact propext h
  · intro h
    subst h
    exact Iff.rfl