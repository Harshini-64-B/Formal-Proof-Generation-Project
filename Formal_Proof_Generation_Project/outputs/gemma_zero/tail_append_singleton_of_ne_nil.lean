theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ []) : (l ++ [a]).tail = l.tail ++ [a] := by
  cases l
  case nil => contradiction
  case cons x xs => rfl