theorem length_map {α β} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp [List.map, List.length, ih]