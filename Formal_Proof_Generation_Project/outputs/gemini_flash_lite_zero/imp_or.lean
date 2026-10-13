theorem not_not_of_not_not_implies_not_not (P : Prop) : ¬¬(¬¬P → P) := by
  intro h
  apply h
  intro hnp
  exfalso
  exact hnp (h (fun hpp => hpp.elim))