theorem list_concat_singleton_rev {α : Type} (x : α) (xs : List α) :
    (xs ++ [x]).reverse = x :: xs.reverse := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [ih]