theorem reverse_reverse {α} (l : List α) : l.reverse.reverse = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [ih]