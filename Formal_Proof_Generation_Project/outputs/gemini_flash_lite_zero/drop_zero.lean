theorem list_reverse_involutive {α : Type*} (l : List α) : l.reverse.reverse = l := by
  exact List.reverse_reverse l