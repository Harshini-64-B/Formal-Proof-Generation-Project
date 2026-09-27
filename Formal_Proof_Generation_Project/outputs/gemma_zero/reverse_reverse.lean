theorem reverse_reverse {α : Type} (l : List α) : l.reverse.reverse = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.reverse]
    rw [List.reverse_append]
    simp [ih]