import Mathlib.Data.List.Basic

theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ []) : (l ++ [a]).tail = l.tail ++ [a] := by
  sorry
