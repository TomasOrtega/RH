import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.ExtraFinal
import Development.AutomorphicSpectrum.Proofs.JetProofs.ExistsDiagonalCongrOfSimilitudeDistinctEigenvalu
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralStmt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos

namespace GlobalTheory.CompanionTheory.Front

/- English proof (translation)
Establish `h` using `GlobalTheory.CompanionTheory.DS.dsUnique`. Unfold `GlobalTheory.CompanionTheory.DS.DSUnique at h`. Unfold `GlobalTheory.Published.DiscreteSeriesUpqUnique`. Use `intros`. Apply the tactic sequence `apply h <;> assumption`.
-/
theorem discreteSeriesUpqUnique : GlobalTheory.Published.DiscreteSeriesUpqUnique := by
  have h := GlobalTheory.CompanionTheory.DS.dsUnique
  unfold GlobalTheory.CompanionTheory.DS.DSUnique at h
  unfold GlobalTheory.Published.DiscreteSeriesUpqUnique
  intros
  apply h <;> assumption

end GlobalTheory.CompanionTheory.Front
