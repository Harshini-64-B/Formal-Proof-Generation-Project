theorem getElem?_length (l : List α) : l[l.length]? = none := by
  simp [List.get?]