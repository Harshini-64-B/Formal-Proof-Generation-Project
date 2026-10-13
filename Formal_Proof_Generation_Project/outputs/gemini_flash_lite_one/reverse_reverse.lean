theorem reverse_reverse {α} (l : List α) : l.reverse.reverse = l := by
  exact List.reverse_reverse l