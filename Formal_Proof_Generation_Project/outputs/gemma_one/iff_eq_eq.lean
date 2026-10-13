theorem iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) := by
  apply propext
  constructor
  · intro h
    exact propext h
  · intro h
    rw [h]
    exact Iff.rfl