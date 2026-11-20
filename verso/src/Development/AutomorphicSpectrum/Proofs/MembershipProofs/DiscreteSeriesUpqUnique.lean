import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.ExtraFinal
import Development.AutomorphicSpectrum.Proofs.JetProofs.ExistsDiagonalCongrOfSimilitudeDistinctEigenvalu
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralStmt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos

namespace GlobalTheory.CompanionTheory.Front

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Fix the arbitrary inputs and assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem discreteSeriesUpqUnique : GlobalTheory.Published.DiscreteSeriesUpqUnique := by
  have h := GlobalTheory.CompanionTheory.DS.dsUnique
  unfold GlobalTheory.CompanionTheory.DS.DSUnique at h
  unfold GlobalTheory.Published.DiscreteSeriesUpqUnique
  intros
  apply h <;> assumption

end GlobalTheory.CompanionTheory.Front
