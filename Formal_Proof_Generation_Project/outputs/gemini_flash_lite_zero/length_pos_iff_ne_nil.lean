theorem length_pos_iff_ne_nil {l : List α} : l ≠ [] ↔ 0 < l.length := by
  cases l with
  | nil => simp
  | cons x xs => simp