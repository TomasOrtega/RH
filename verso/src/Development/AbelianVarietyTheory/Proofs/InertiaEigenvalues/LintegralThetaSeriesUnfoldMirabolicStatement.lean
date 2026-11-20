import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.MirTower
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaUnfold.lintegral_theta_unfold` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLintegralThetaSeriesUnfoldMirabolic.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.lintegral_theta_series_unfold_mirabolic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕P μ → ∀ F : GA E a → (Fin a → Ad E) → ℝ≥0∞, (∀ v : Fin a → E, Measurable fun g : GA E a => F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val)) → (∀ (γ : GL (Fin a) E) g y, F (ratGL E a γ * g) y = F g y) → ∫⁻ g in 𝓕, ∑' ξ : {v : Fin a → E // v ≠ 0}, F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ.1 i)) g.val) ∂μ = ∫⁻ g in 𝓕P, F g (g.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩) ∂μ := by
  first | exact @GlobalTheory.ThetaUnfold.lintegral_theta_unfold | exact GlobalTheory.ThetaUnfold.lintegral_theta_unfold | (intros; apply GlobalTheory.ThetaUnfold.lintegral_theta_unfold <;> assumption)
