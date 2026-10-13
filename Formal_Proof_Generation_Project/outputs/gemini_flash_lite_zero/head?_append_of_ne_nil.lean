theorem list_concat_singleton_rev {α : Type*} (x : α) (xs : List α) :
    (xs ++ [x]).reverse = x :: xs.reverse := by
  simp