import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MeasurableFibreCountOver
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Short.Crofton.measurable_cntOver` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FMeasurableFibreCountOver.lean&line=127#L127)
-/
theorem _root_.GlobalTheory.T.measurable_fibre_count_over : ∀ (n m : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsSigmaCompact S →
  Measurable (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) => cntOver S p.1 p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.measurable_cntOver | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.measurable_cntOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.measurable_cntOver <;> assumption)
