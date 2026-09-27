theorem replicate_add (m n) (a : α) : List.replicate (m + n) a = List.replicate m a ++ List.replicate n a := by
  induction m with
  | zero => simp
  | succ m ih => simp [Nat.succ_add, ih]