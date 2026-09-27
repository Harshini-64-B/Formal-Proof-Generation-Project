theorem replicate_add (m n) (a : α) : List.replicate (m + n) a = List.replicate m a ++ List.replicate n a := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [List.replicate, ih]