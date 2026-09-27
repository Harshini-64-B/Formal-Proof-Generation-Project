theorem cons_head!_tail [Inhabited α] (l : List α) (h : l ≠ []) : l.head! :: l.tail = l := by
  cases l with
  | nil => contradiction
  | cons x xs => rfl