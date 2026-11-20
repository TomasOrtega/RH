import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoAverageL2Compact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarCompactLtTop
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FTendstoAverageL2Compact.lean&line=189#L189)
-/
theorem _root_.GlobalTheory.T.tendsto_average_L2_compact : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → ∀ {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (g : Mt k r → Wp), (∀ K : Set (Mt k r), IsCompact K → AEStronglyMeasurable g (μ.restrict K) ∧ ∫⁻ x in K, (‖g x‖₊ : ENNReal) ^ 2 ∂μ < ⊤) → ∀ K : Set (Mt k r), IsCompact K → Filter.Tendsto (fun j : ℕ => ∫⁻ x in K, (‖avgR μ j g x - g x‖₊ : ENNReal) ^ 2 ∂μ) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.SgInf.tendsto_average_L2 | exact GlobalTheory.SgInf.tendsto_average_L2 | (intros; apply GlobalTheory.SgInf.tendsto_average_L2 <;> assumption)
