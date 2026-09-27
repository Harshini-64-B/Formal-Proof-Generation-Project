theorem length_reverse {α} (l : List α) : l.reverse.length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.reverse, List.length, ih]