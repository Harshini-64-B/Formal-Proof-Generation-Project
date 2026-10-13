import Mathlib.Data.List.Basic

-- Ex.7. If a list has length n + 1 (that is, a positive length), then the list is nonempty. More precisely, there exist an element h (the head) and a list t (the tail) such that the list is exactly h :: t.
theorem exists_of_length_succ {n} : ∀ (l : List α), l.length = n + 1 → ∃ h t, l = h :: t := by
  intro l h
  cases l with
  | nil => rw[List.length_nil] at h; contradiction
  | cons a b => simp
