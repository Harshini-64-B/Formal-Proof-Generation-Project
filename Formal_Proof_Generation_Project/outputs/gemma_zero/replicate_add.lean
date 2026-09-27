theorem replicate_add (m n : Nat) (a : α) : List.replicate (m + n) a = List.replicate m a ++ List.replicate n a := by
  induction m with
  | zero => 
    simp [List.replicate, Nat.add_zero]
  | succ m ih => 
    simp [List.replicate, Nat.succ_add, ih]