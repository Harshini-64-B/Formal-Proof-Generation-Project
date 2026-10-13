theorem append_left_injective (t : List α) : Function.Injective fun (s : List α) => s ++ t := by
  intro a b h
  exact List.append_right_cancel h