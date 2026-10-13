theorem getElem?_length (l : List α) : l[l.length]? = none := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]