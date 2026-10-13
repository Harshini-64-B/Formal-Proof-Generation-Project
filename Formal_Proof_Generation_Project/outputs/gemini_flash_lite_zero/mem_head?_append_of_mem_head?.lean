theorem list_append_nil {α : Type} (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => rw [List.cons_append, ih]