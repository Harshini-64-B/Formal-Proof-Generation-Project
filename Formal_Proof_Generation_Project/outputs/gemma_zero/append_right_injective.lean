theorem append_right_injective (s : List α) : Function.Injective fun (t : List α) => s ++ t := by
  intro t1 t2 h
  induction s with
  | nil => exact h
  | cons a as ih =>
    rw [List.append_cons] at h
    exact ih (congr_arg List.tail h)