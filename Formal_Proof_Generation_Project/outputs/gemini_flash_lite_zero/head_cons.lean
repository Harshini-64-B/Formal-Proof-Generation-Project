theorem list_append_nil {α : Type} (l : List α) : l ++ [] = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [ih]