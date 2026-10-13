theorem take_length {α} (l : List α) : l.take l.length = l := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp [List.take, List.length_cons]
    rw [ih]