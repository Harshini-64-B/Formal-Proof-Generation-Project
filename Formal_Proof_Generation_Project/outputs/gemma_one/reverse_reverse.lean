theorem reverse_reverse {α} (l : List α) : l.reverse.reverse = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp [List.reverse]
    rw [List.reverse_append]
    rw [ih]
    simp [List.reverse]