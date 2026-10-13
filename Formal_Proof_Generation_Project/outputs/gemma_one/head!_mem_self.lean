theorem head!_mem_self [Inhabited α] (l : List α) (h : l ≠ []) : l.head! ∈ l := by
  cases l with
  | nil => contradiction
  | cons a t => simp [List.head!]