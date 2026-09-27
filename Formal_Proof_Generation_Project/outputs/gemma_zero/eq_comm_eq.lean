theorem eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a) := by
  apply propext
  exact eq_comm