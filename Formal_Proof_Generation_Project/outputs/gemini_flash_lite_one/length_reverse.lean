theorem length_reverse {α} (l : List α) : l.reverse.length = l.length := by
  induction' l with x l ih
  · rfl
  · simp [ih]