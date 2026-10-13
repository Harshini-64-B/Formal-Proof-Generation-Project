theorem zero_add_eq_id {M : Type u_4} [AddZeroClass M] : (fun (x : M) => 0 + x) = id := by
  ext x
  exact zero_add x