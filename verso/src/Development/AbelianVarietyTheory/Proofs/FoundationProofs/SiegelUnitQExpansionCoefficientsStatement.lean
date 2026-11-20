import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitQExpansionCoefficients
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KExp.siegel_exp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSiegelUnitQExpansionCoefficients.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.siegel_unit_q_expansion_coefficients : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b : ℕ), 0 < M → a < M → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → ∃ (k : ℤ) (A : ℕ → Ω), GlobalTheory.QFam.HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => ε (A n)) ∧ (∀ n : ℕ, (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff (((k : ℚ) + n) / M) = A n) ∧ ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff r = 0 := by
  first | exact @GlobalTheory.KExp.siegel_exp | exact GlobalTheory.KExp.siegel_exp | (intros; apply GlobalTheory.KExp.siegel_exp <;> assumption)
