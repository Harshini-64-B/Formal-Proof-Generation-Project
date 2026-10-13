theorem append_left_injective (t : List α) : Function.Injective fun (s : List α) => s ++ t := by
  intro s1 s2 h
  have h_len : s1.length = s2.length := by
    rw [List.length_append] at h
    exact Nat.add_left_cancel h
  induction s1 with
  | nil =>
    exact List.length_eq_zero_iff.mpr h_len
  | cons a s1' ih =>
    cases s2 with
    | nil =>
      exact Nat.succ_ne_zero s1'.length |>.elim (by simp [h_len])
    | cons b s2' =>
      have h_head : a = (s1 ++ t).head := by rw [List.app_cons, List.head_cons]
      have h_head2 : b = (s2 ++ t).head := by rw [List.app_cons, List.head_cons]
      have h_tail : s1' ++ t = (s1 ++ t).tail := by rw [List.app_cons, List.tail_cons]
      have h_tail2 : s2' ++ t = (s2 ++ t).tail := by rw [List.app_cons, List.tail_cons]
      have h_head_eq : (s1 ++ t).head = (s2 ++ t).head := by rw [h]
      rw [h_head, h_head2] at h_head_eq
      have h_tail_eq : (s1 ++ t).tail = (s2 ++ t).tail := by rw [h]
      rw [h_tail, h_tail2] at h_tail_eq
      rw [h_tail_eq] at ih
      exact ih