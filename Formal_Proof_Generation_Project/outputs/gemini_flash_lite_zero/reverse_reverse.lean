theorem reverse_reverse {α} (l : List α) : l.reverse.reverse = l := by
  induction' l with x l ih
  · rfl
  · simp [ih]