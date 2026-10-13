theorem length_pos_iff_ne_nil {l : List α} : l ≠ [] ↔ 0 < l.length := by
  constructor
  · intro h
    cases l with
    | nil => contradiction
    | cons _ _ => simp
  · intro h
    cases l with
    | nil => contradiction
    | cons _ _ => simp