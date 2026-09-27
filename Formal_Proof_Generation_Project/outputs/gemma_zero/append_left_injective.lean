theorem append_left_injective (t : List α) : Function.Injective fun (s : List α) => s ++ t := by
  intro s1 s2 h
  exact List.append_right_inj.mp h