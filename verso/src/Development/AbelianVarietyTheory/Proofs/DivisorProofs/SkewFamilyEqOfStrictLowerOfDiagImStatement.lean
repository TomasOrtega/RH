import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewFamilyEqOfStrictLowerOfDiagIm
import Mathlib
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.skewFamily_eq_of_strictLower_of_diagIm` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSkewFamilyEqOfStrictLowerOfDiagIm.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.skew_family_eq_of_strictLower_of_diagIm : ∀ {ι : Type} [Fintype ι] {r : ℕ} (s : Fin r → ℝ), (∀ a, s a * s a = 1) → ∀ (Y Y' : ι × Fin r × Fin r → ℂ), (∀ τ a b, Y (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y (τ, a, b))) → (∀ τ, ∑ a, Y (τ, a, a) = 0) → (∀ τ a b, Y' (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y' (τ, a, b))) → (∀ τ, ∑ a, Y' (τ, a, a) = 0) → (∀ τ a b, b < a → Y (τ, a, b) = Y' (τ, a, b)) → (∀ τ (a : Fin r), (a : ℕ) + 1 < r → (Y (τ, a, a)).im = (Y' (τ, a, a)).im) → Y = Y' := by
  first | exact @GlobalTheory.skewFamily_eq_of_strictLower_of_diagIm | exact GlobalTheory.skewFamily_eq_of_strictLower_of_diagIm | (intros; apply GlobalTheory.skewFamily_eq_of_strictLower_of_diagIm <;> assumption)
