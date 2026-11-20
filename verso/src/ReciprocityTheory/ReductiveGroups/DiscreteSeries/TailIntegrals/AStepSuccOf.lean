import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.AStepFin

namespace ReciprocityTheory.ChartRestriction.DS.Xi

/- English proof (translation)
Introduce `k r r' hr hk hA`. Substitute `hr` using the available equality. Conclude with `StepA.aStep_fin hB2 hIW hT hF hCH k r' hk hA`.
-/
theorem aStepSucc_of (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hF : FormulaF) (hCH : CH) : AStepSucc := by
  intro k r r' hr hk hA
  subst hr
  exact StepA.aStep_fin hB2 hIW hT hF hCH k r' hk hA

end ReciprocityTheory.ChartRestriction.DS.Xi
