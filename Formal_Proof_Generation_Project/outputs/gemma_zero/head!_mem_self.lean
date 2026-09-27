theorem head!_mem_self [Inhabited α] (l : List α) (h : l ≠ []) : l.head! ∈ l := by
  match l with
  | [] => contradiction h
  | x :: xs => simp [List.head!, List.mem]