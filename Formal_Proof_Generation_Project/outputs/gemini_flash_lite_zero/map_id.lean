theorem map_id {α} (l : List α) : List.map (id : α → α) l = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]