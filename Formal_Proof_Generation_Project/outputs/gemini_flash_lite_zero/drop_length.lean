theorem drop_length {α} (l : List α) : l.drop l.length = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih => exact ih