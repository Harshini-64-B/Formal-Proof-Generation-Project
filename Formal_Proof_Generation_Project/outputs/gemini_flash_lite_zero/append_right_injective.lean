theorem append_right_injective (s : List α) : Function.Injective fun (t : List α) => s ++ t := by
  intro a b h
  exact List.append_left_cancel s h