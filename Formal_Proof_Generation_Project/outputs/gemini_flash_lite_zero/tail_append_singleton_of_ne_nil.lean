theorem list_rev_nil_inv {α : Type u} (l : List α) (h : l.reverse = []) : l = [] := by
  cases l with
  | nil => rfl
  | cons x xs => contradiction