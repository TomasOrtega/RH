import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParsevalContinuousPeriodicAdelicRationalQuotient
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FParsevalContinuousPeriodicAdelicRationalQuotient.lean&line=181#L181)
-/
theorem _root_.GlobalTheory.T.parseval_continuous_periodic_adelicRationalQuotient : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ Φ : (ι → Ad E) → ℂ, Per (ratV E ι) Φ → ∀ [MeasurableSpace (ι → Ad E)] [BorelSpace (ι → Ad E)] (ν : Measure (ι → Ad E)) (D : Set (ι → Ad E)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratV E ι) D ν → ν D = 1 → ∑' ξ : ι → E, ‖avg (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x)‖ₑ ^ 2 = ∫⁻ x in D, ‖Φ x‖ₑ ^ 2 ∂ν := by
  first | exact @GlobalTheory.AdelicParseval.tsum_enorm_avg_sq | exact GlobalTheory.AdelicParseval.tsum_enorm_avg_sq | (intros; apply GlobalTheory.AdelicParseval.tsum_enorm_avg_sq <;> assumption)
