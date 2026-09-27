theorem ne_nil_of_length_pos {l : List α} (h: 0 < l.length) : l ≠ [] := by
  intro h_nil
  subst h_nil
  exact Nat.lt_irrefl 0 h