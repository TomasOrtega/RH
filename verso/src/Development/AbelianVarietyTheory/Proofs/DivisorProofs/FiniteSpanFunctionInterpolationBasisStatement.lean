import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSpanFunctionInterpolationBasis
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_interpolation_basis` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteSpanFunctionInterpolationBasis.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.finite_span_function_interpolation_basis : ∀ (Y : Type) (r : ℕ) (g : Fin r → Y → ℂ), ∃ (r' : ℕ) (g' : Fin r' → Y → ℂ) (c : Fin r' → Y),
    (∀ j, g' j ∈ Submodule.span ℂ (Set.range g)) ∧
    ∀ φ ∈ Submodule.span ℂ (Set.range g), ∀ y, φ y = ∑ j, φ (c j) * g' j y := by
  first | exact @GlobalTheory.exists_interpolation_basis | exact GlobalTheory.exists_interpolation_basis | (intros; apply GlobalTheory.exists_interpolation_basis <;> assumption)
