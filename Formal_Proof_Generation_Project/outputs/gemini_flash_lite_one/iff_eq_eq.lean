theorem iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) := by
  ext
  constructor
  · intro h
    ext
    exact h
  · intro h
    subst h
    rfl