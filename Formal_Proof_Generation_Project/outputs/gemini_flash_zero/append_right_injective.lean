import Mathlib.Logic.Function.Basic

theorem append_right_injective (s : List α) : Function.Injective fun (t : List α) => s ++ t := by
  intro t1 t2 h
  induction s with
  | nil => exact h
  | cons x xs ih =>
    apply ih
    injection h with _ h'
    exact h'