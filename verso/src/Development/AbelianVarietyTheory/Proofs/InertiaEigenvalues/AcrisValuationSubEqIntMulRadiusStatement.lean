import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationSubEqIntMulRadius
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.Gauss.vr_sub_eq_int_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAcrisValuationSubEqIntMulRadius.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l, (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w ≠ 0 → w' ≠ 0 → φc l w * w' = w * φc l w' → ∃ n : ℤ, ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r w - vr l r w' = n * r := by
  first | exact @GlobalTheory.PMon.Gauss.vr_sub_eq_int_mul | exact GlobalTheory.PMon.Gauss.vr_sub_eq_int_mul | (intros; apply GlobalTheory.PMon.Gauss.vr_sub_eq_int_mul <;> assumption)
