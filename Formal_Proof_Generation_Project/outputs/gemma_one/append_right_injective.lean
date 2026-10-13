theorem append_right_injective (s : List α) : Function.Injective fun (t : List α) => s ++ t := by
  intro t1 t2 h
  exact List.left_cancel h