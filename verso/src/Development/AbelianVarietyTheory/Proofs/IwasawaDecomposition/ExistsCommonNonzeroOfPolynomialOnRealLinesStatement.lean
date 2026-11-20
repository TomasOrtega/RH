import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonNonzeroOfPolynomialOnRealLines
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_common_nonzero_of_polynomial_on_lines` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsCommonNonzeroOfPolynomialOnRealLines.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.exists_common_nonzero_of_polynomial_on_real_lines : ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (ι : Type) [Finite ι] (f : ι → V → ℂ), (∀ i a b, ∃ p : Polynomial ℂ, ∀ s : ℝ, f i (a + s • b) = p.eval (s : ℂ)) → (∀ i, ∃ v, f i v ≠ 0) → ∃ v, ∀ i, f i v ≠ 0 := by
  first | exact @GlobalTheory.exists_common_nonzero_of_polynomial_on_lines | exact GlobalTheory.exists_common_nonzero_of_polynomial_on_lines | (intros; apply GlobalTheory.exists_common_nonzero_of_polynomial_on_lines <;> assumption)
