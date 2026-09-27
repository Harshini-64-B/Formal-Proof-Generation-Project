theorem one_mul_eq_id {M : Type u_4} [MulOneClass M] : (fun (x : M) => 1 * x) = id := by
  funext x
  exact one_mul x