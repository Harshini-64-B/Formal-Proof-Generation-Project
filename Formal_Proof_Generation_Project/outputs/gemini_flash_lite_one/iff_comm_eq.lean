theorem iff_comm_eq (a b : Prop) : (a ↔ b) = (b ↔ a) := by
  ext
  constructor
  · intro h
    constructor <;> exact h.symm
  · intro h
    constructor <;> exact h.symm