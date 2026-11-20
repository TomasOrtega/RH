import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.AStepFin

namespace ReciprocityTheory.ChartRestriction.DS.Xi

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem aStepSucc_of (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hF : FormulaF) (hCH : CH) : AStepSucc := by
  intro k r r' hr hk hA
  subst hr
  exact StepA.aStep_fin hB2 hIW hT hF hCH k r' hk hA

end ReciprocityTheory.ChartRestriction.DS.Xi
