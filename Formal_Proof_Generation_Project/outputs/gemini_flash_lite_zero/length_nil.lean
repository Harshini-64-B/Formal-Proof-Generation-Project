theorem list_append_nil {α : Type} (l : List α) : l ++ [] = l := by
  induction' l with x l ih
  · rfl
  · simp [ih]