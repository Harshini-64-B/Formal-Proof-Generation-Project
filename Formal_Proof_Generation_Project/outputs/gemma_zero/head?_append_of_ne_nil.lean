theorem head?_append_of_ne_nil : ∀ (a : List α) {b : List α} (_ : a ≠ []), (a ++ b).head? = a.head? := by
  intro a ha
  match a with
  | [] => contradiction
  | x :: xs => rfl