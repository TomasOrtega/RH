import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFunctionalIterPartialDeriv
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsContinuousFunctionalIterPartialDeriv.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.exists_continuous_functional_iterPartialDeriv : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (R : B →ₗ[ℂ] (E d → ℂ)), (∀ x ∈ U, Continuous fun u => R u x) → (∀ u, ContDiffOn ℝ ∞ (R u) U) → ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : B →L[ℂ] ℂ, ∀ u, l u = dw w (R u) x := by
  first | exact @GlobalTheory.HCA.dw_continuousFunctional | exact GlobalTheory.HCA.dw_continuousFunctional | (intros; apply GlobalTheory.HCA.dw_continuousFunctional <;> assumption)
