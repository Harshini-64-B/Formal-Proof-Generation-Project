theorem getElem?_length (l : List α) : l[l.length]? = none := by
  induction l with
  | nil => rfl
  | cons a as ih => exact ih