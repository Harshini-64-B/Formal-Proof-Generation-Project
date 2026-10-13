theorem list_append_nil (l : List α) : l ++ [] = l := by
  exact List.append_nil l