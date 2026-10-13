theorem ne_nil_of_length_pos {l : List α} (h: 0 < l.length) : l ≠ [] := by
  intro hl
  rw [hl] at h
  exact Nat.lt_irrefl 0 h