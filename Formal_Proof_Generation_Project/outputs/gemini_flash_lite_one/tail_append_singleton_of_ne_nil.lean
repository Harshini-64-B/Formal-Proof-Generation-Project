theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ []) : (l ++ [a]).tail = l.tail ++ [a] := by
  cases l with
  | nil => contradiction
  | cons x xs => rfl