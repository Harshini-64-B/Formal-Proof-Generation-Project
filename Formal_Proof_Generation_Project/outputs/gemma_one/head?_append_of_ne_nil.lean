theorem head?_append_of_ne_nil : ∀ (a : List α) {b : List α} (_ : a ≠ []), (a ++ b).head? = a.head? := by
  intro a h_ne_nil
  cases a with
  | nil => contradiction
  | cons x xs => simp [List.append_cons]