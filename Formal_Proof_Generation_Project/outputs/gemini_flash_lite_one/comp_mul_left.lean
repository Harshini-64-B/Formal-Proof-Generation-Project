theorem comp_mul_left {α : Type u_1} [Semigroup α] (x y : α) : ((fun (x_1 : α) => x * x_1) ∘ fun (x : α) => y * x) = fun (x_1 : α) => x * y * x_1 := by
  ext z
  dsimp
  rw [mul_assoc]