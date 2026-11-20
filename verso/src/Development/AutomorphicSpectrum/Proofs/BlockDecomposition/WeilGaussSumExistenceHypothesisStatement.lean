import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilGaussSumExistenceHypothesis
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeilGaussSumExistenceHypothesis.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.weil_gauss_sum_existence_hypothesis : Ad3.K.GL2LocalData.WGaussEx := by
  first | exact @GlobalTheory.CompanionTheory.WGaussEx.wGaussEx | exact GlobalTheory.CompanionTheory.WGaussEx.wGaussEx | (intros; apply GlobalTheory.CompanionTheory.WGaussEx.wGaussEx <;> assumption)
