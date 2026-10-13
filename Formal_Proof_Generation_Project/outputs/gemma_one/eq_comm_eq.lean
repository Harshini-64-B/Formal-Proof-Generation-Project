theorem eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a) := by
  apply propext
  constructor
  · intro h
    exact Eq.symm h
  · intro h
    exact Eq.symm h