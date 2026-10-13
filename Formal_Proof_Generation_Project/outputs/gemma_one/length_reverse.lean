theorem length_reverse {α} (l : List α) : l.reverse.length = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp [List.reverse, ih]
    rw [List.reverse_append_length]
    simp