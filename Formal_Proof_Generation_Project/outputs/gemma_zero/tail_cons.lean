theorem tail_cons {α} (a : α) (l : List α) : (a :: l).tail = l := by
  rfl