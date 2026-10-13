theorem replicate_add (m n : Nat) (a : α) : List.replicate (m + n) a = List.replicate m a ++ List.replicate n a := by
  induction m with
  | zero => simp [List.replicate_zero, Nat.zero_add]
  | succ m ih => simp [List.replicate_succ, ih]
    rw [List.cons_append]
    simp