import Mathlib.Data.List.Basic

theorem cons_head!_tail [Inhabited α] (l : List α) (h : l ≠ []) : l.head! :: l.tail = l := by
  sorry
