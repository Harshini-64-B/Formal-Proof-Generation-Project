theorem iff_comm_eq (a b : Prop) : (a ↔ b) = (b ↔ a) := by
  apply propext
  constructor
  · intro h
    exact h.symm
  · intro h
    exact h.symm