import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEq
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FEqOfSiegelThetaSeriesRationalEq.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.eq_of_siegelThetaSeriesRational_eq : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ ψ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB ψ → ∀ τ ∈ Siegel ι, (∀ ζ, thS φ τ ζ = thS ψ τ ζ) → φ = ψ := by
  first | exact @GlobalTheory.SW.eq_of_thS_eq | exact GlobalTheory.SW.eq_of_thS_eq | (intros; apply GlobalTheory.SW.eq_of_thS_eq <;> assumption)
