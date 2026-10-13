theorem mem_cons_self (x : α) (l : List α) : x ∈ (x :: l) := by
  exact List.Mem.head l