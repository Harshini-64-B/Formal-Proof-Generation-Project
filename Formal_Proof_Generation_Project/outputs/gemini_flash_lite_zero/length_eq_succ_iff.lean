theorem list_append_nil {α : Type} (l : List α) : l ++ [] = l := by
  exact List.append_nil l