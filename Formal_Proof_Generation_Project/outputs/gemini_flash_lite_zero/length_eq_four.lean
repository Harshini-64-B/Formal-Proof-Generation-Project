theorem list_reverse_involutive {α : Type u} (l : List α) : l.reverse.reverse = l := by
  exact List.reverse_reverse l