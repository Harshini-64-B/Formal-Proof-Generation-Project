import Mathlib.Logic.Function.Basic
import Mathlib.Data.List.Basic

theorem append_left_injective (t : List α) : Function.Injective fun (s : List α) => s ++ t := by
  intro s1 s2 h
  exact List.append_cancel_right h