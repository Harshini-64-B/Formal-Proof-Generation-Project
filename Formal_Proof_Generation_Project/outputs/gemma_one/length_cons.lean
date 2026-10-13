theorem length_cons (a : α) (l : List α) : (a :: l).length = l.length + 1 := by
  simp