theorem length_pos_of_ne_nil {l : List α} (h: l ≠ []) : 0 < l.length := by
  cases l
  · contradiction
  · simp