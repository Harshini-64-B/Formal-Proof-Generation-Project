theorem cons_ne_nil {α} (a : α) (l : List α) : a :: l ≠ [] := by
  intro h
  cases h