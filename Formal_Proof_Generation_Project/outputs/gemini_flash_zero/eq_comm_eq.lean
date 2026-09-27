theorem eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a) := by
  exact propext ⟨Eq.symm, Eq.symm⟩