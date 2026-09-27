theorem iff_comm_eq (a b : Prop) : (a ↔ b) = (b ↔ a) := by
  ext
  simp [iff_comm]