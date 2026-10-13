import Mathlib.Data.List.Basic

-- Ex.9. If replicating the element a m times produces the same list as replicating a n times, then m = n.
theorem replicate_left_injective (a : α) : Function.Injective (List.replicate · a) := by
  unfold Function.Injective
  intro m n h
  have h_len := congrArg List.length h
  simp at h_len
  exact h_len
