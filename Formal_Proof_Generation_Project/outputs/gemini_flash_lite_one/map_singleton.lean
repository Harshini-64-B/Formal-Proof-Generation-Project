theorem map_singleton {α β} (f : α → β) (a : α) : List.map f [a] = [f a] := by
  rfl