theorem length_pos_of_ne_nil {l : List α} (h: l ≠ []) : 0 < l.length := by
  cases l with
  | nil => contradiction
  | cons x xs => exact Nat.succ_pos _