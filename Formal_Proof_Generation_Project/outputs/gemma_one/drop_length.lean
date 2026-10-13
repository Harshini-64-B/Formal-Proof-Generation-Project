theorem drop_length {α} (l : List α) : l.drop l.length = [] := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp [List.drop, List.length]
    rw [ih]