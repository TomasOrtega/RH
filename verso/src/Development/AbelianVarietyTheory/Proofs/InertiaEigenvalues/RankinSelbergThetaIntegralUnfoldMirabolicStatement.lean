import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralUnfoldMirabolic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FRankinSelbergThetaIntegralUnfoldMirabolic.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.rankinSelbergThetaIntegral_unfold_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ →
    ∀ φ φ' : GA E (m + 1) → ℂ, Measurable φ → Measurable φ' → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ γ g, φ' (ratGL E (m + 1) γ * g) = φ' g) → ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), Continuous Φ → ∀ x : ℝ,
    ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ →
    Zint μ 𝓕 φ φ' Φ N x = ∫ g in 𝓕P, Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) ∂μ := by
  first | exact @GlobalTheory.ZUnfTheta.zint_eq_mirabolic | exact GlobalTheory.ZUnfTheta.zint_eq_mirabolic | (intros; apply GlobalTheory.ZUnfTheta.zint_eq_mirabolic <;> assumption)
