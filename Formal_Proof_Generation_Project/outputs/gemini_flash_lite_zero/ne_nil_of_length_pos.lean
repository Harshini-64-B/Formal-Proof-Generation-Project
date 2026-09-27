theorem ne_nil_of_length_pos {l : List α} (h: 0 < l.length) : l ≠ [] := by
  intro heq
  subst heq
  contradiction