import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumAtCuspHahnCoeffOfIntegralExponents
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHeckeSumAtCuspHahnCoeffOfIntegralExponents.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.heckeSumAtCuspHahn_coeff_of_integral_exponents : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ), 0 < q → ∀ φ : HahnSeries ℚ Ω,
  (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → ∀ s : ℚ, (hq ε q φ).coeff s = if s.den = 1 then φ.coeff ((q : ℚ) * s) else 0 := by
  first | exact @GlobalTheory.HeckeInt.hq_coeff_of_int | exact GlobalTheory.HeckeInt.hq_coeff_of_int | (intros; apply GlobalTheory.HeckeInt.hq_coeff_of_int <;> assumption)
