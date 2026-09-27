theorem length_map {α β} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]