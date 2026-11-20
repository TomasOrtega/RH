import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformCasimirReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCoshTransformCasimirReal.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.cosh_transform_casimir_real : ∀ (n : ℕ) (χ : Inf n) (g : ℝ → ℝ) (T : ℝ), IsHerm χ → IsBump g T → conj (coshT g (cas χ)) = coshT g (cas χ) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas | exact GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas | (intros; apply GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas <;> assumption)
