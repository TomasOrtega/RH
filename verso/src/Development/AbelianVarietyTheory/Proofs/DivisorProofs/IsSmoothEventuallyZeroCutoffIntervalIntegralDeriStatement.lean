import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothEventuallyZeroCutoffIntervalIntegralDeri
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsSmoothEventuallyZeroCutoffIntervalIntegralDeri.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.isSmoothEventuallyZeroCutoff_intervalIntegral_deriv : ∀ (F : ℝ → ℝ → ℝ) (a b : ℝ), ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) → (∃ R : ℝ, ∀ s ∈ Set.uIcc a b, ∀ y, R ≤ y → F s y = 0) → GlobalTheory.PsCo.Pc1.IsCutFn (fun y => ∫ s in a..b, F s y) ∧ ∀ y, deriv (fun y => ∫ s in a..b, F s y) y = ∫ s in a..b, deriv (F s) y := by
  first | exact @GlobalTheory.PsCo.Pc1.isCutFn_intervalIntegral_and_deriv | exact GlobalTheory.PsCo.Pc1.isCutFn_intervalIntegral_and_deriv | (intros; apply GlobalTheory.PsCo.Pc1.isCutFn_intervalIntegral_and_deriv <;> assumption)
