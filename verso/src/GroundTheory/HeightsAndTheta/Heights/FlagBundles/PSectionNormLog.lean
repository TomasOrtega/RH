import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped InnerProductSpace ComplexConjugate

noncomputable section

/- English proof (translation)
Establish `h1 : ‖(Submodule.Quotient.mk x : E ⧸ U)‖ = Metric.infDist x (U : Set E)` using `QuotientAddGroup.norm_mk (S := U.toAddSubgroup) x`. Rewrite using `[h1, Metric.infDist_eq_iInf, Submodule.starProjection_minimal]`. Simplify using `only [dist_eq_norm]`. Both sides reduce to the same expression.
-/
theorem quotient_norm_eq_norm_sub_starProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (U : Submodule ℂ E) [U.HasOrthogonalProjection] (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ U)‖ = ‖x - U.starProjection x‖ := by
  have h1 : ‖(Submodule.Quotient.mk x : E ⧸ U)‖ = Metric.infDist x (U : Set E) :=
    QuotientAddGroup.norm_mk (S := U.toAddSubgroup) x
  rw [h1, Metric.infDist_eq_iInf, Submodule.starProjection_minimal]
  simp only [dist_eq_norm]
  rfl

/- English proof (translation)
Rewrite using `[quotient_norm_eq_norm_sub_starProjection, Submodule.starProjection_unit_singleton ℂ h₂, @norm_sub_sq ℂ, inner_smul_right, norm_smul, h₁, h₂, mul_one, ← inner_conj_symm e₁ e₂, Complex.norm_conj, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]`. Rewrite using `[RCLike.re_to_complex, Complex.ofReal_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quotient_norm_sq_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e₁ e₂ : E) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) :
    ‖(Submodule.Quotient.mk e₁ : E ⧸ ℂ ∙ e₂)‖ ^ 2 = 1 - ‖⟪e₁, e₂⟫_ℂ‖ ^ 2 := by
  rw [quotient_norm_eq_norm_sub_starProjection, Submodule.starProjection_unit_singleton ℂ h₂,
    @norm_sub_sq ℂ, inner_smul_right, norm_smul, h₁, h₂, mul_one, ← inner_conj_symm e₁ e₂,
    Complex.norm_conj, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  rw [RCLike.re_to_complex, Complex.ofReal_re]
  ring

/- English proof (translation)
Introduce `e₁ e₂ h₁ h₂`. Establish `hsq` using `quotient_norm_sq_line e₁ e₂ h₁ h₂`. Use `⟨hsq, fun _ => ?_⟩` and prove the remaining obligations. Rewrite `hsq` using `[h0.2 e₁ e₂ h₁ h₂]`. Unfold `kernelL`.

Use `set q := ‖(Submodule.Quotient.mk e₁ : EuclideanSpace ℂ (Fin 2) ⧸ ℂ ∙ e₂)‖`. Establish `: (1 - ⟪blochVector e₁, blochVector e₂⟫_ℝ) / 2 = q ^ 2` using `by rw [hsq]; ring`. Rewrite using `[this, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem SectionNormLog.proof (h0 : BlochOverlap.Statement) : SectionNormLog.Statement := by
  intro e₁ e₂ h₁ h₂
  have hsq := quotient_norm_sq_line e₁ e₂ h₁ h₂
  refine ⟨hsq, fun _ => ?_⟩
  rw [h0.2 e₁ e₂ h₁ h₂] at hsq
  unfold kernelL
  set q := ‖(Submodule.Quotient.mk e₁ : EuclideanSpace ℂ (Fin 2) ⧸ ℂ ∙ e₂)‖
  have : (1 - ⟪blochVector e₁, blochVector e₂⟫_ℝ) / 2 = q ^ 2 := by rw [hsq]; ring
  rw [this, Real.log_pow]
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.FlagBundles
