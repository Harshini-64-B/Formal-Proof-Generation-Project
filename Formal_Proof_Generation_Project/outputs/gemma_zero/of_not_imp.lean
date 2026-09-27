theorem of_not_imp {a b : Prop} : ¬(a → b) → a := by
  intro h
  by_contra ha
  exact h (fun x => Classical.False.elim (ha x))