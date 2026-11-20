import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicProductFormula
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPAdicProductFormula.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.p_adic_product_formula : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (a : K), a ≠ 0 → ∑ᶠ j : K →+* ℂ_[p], Real.log ‖j a‖ = -((padicValRat p (Algebra.norm ℚ a) : ℝ) * Real.log p) := by
  first | exact @GlobalTheory.sum_log_norm_embeddings_padicComplex | exact GlobalTheory.sum_log_norm_embeddings_padicComplex | (intros; apply GlobalTheory.sum_log_norm_embeddings_padicComplex <;> assumption)
