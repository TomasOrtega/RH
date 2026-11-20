import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilGaussConstantHypothesis
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GaussLam.wGaussLam` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeilGaussConstantHypothesis.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.weil_gauss_constant_hypothesis : Ad3.K.GL2LocalData.WGaussLam := by
  first | exact @GlobalTheory.CompanionTheory.GaussLam.wGaussLam | exact GlobalTheory.CompanionTheory.GaussLam.wGaussLam | (intros; apply GlobalTheory.CompanionTheory.GaussLam.wGaussLam <;> assumption)
