theorem take_length {α} (l : List α) : l.take l.length = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.take_succ, ih]