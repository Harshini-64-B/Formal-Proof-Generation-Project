theorem append_nil (l : List α) : l ++ [] = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [ih]