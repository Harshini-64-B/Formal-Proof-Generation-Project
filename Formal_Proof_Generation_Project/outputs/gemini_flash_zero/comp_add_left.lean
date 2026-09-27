theorem comp_add_left {α : Type u_1} [AddSemigroup α] (x y : α) : 
    ((fun (x_1 : α) => x + x_1) ∘ fun (x : α) => y + x) = fun (x_1 : α) => x + y + x_1 := by
  funext z
  exact (add_assoc x y z).symm