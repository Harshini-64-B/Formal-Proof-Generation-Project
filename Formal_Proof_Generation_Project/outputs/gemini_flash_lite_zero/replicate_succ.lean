theorem replicate_succ {a : α} {n : Nat} : List.replicate (n + 1) a = a :: List.replicate n a := by
  rfl