theorem head_cons {α} (a : α) (l : List α) {h} : (a :: l).head h = a := by
  rfl