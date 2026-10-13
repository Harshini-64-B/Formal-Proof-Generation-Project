theorem list_reverse_involutive (l : List α) : l.reverse.reverse = l := by
  exact List.reverse_reverse l