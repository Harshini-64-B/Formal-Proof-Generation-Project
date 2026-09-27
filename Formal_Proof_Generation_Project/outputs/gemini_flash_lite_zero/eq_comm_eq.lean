theorem eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a) := by
  ext
  constructor <;> intro h <;> rw [h]