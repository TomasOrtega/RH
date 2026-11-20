import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilGaussSumExistenceHypothesis
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.WGaussEx.wGaussEx | exact GlobalTheory.CompanionTheory.WGaussEx.wGaussEx | (intros; apply GlobalTheory.CompanionTheory.WGaussEx.wGaussEx <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.weil_gauss_sum_existence_hypothesis : Ad3.K.GL2LocalData.WGaussEx := by
  first | exact @GlobalTheory.CompanionTheory.WGaussEx.wGaussEx | exact GlobalTheory.CompanionTheory.WGaussEx.wGaussEx | (intros; apply GlobalTheory.CompanionTheory.WGaussEx.wGaussEx <;> assumption)
