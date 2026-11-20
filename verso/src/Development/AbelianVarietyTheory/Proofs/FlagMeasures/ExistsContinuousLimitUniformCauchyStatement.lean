import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousLimitUniformCauchy
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarCompactLtTop
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsContinuousLimitUniformCauchy.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.exists_continuous_limit_uniformCauchy : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → ∀ {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [CompleteSpace Wp] (f : ℕ → Mat k r → Wp) (g : Mt k r → Wp), (∀ j, ContinuousOn (f j) (GG k r)) → (∀ Q : Set (Mt k r), IsCompact Q → AEStronglyMeasurable g (μ.restrict Q)) → (∀ Q : Set (Mt k r), IsCompact Q → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ l ≥ N, ∀ x ∈ Q, Matrix.of x ∈ GG k r → ‖f j (Matrix.of x) - f l (Matrix.of x)‖ ≤ ε) → (∀ Q : Set (Mt k r), IsCompact Q → Filter.Tendsto (fun j : ℕ => ∫⁻ x in Q, (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 ∂μ) Filter.atTop (nhds 0)) → ∃ F : Mat k r → Wp, ContinuousOn F (GG k r) ∧ ((fun x : Mt k r => F (Matrix.of x)) =ᵐ[μ] g) ∧ ∀ x ∈ GG k r, Filter.Tendsto (fun j : ℕ => f j x) Filter.atTop (nhds (F x)) := by
  first | exact @GlobalTheory.SgInf.RegLimit.exists_continuous_limit | exact GlobalTheory.SgInf.RegLimit.exists_continuous_limit | (intros; apply GlobalTheory.SgInf.RegLimit.exists_continuous_limit <;> assumption)
