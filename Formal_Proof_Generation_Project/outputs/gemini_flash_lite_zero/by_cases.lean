theorem not_not_of_not_not_implies (P : Prop) : ¬¬¬P → ¬P := by
  intro hnp hlp
  apply hnp
  intro hlp2
  exact hlp2 hlp