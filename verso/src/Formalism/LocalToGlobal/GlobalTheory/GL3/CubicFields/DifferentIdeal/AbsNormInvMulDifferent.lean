import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.LineR

noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem absNorm_galois_smul' (E : Type) [Field E] [NumberField E] (c : E ≃ₐ[ℚ] E) (𝔟 : Ideal (𝓞 E)) :
    Ideal.absNorm (c • 𝔟) = Ideal.absNorm 𝔟 := by
  classical
  rw [Ideal.pointwise_smul_def]
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv 𝔟 _ (MulSemiringAction.toRingEquiv _ (𝓞 E) c) rfl).toEquiv).symm

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem absNorm_inv_mul_different (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
    [Algebra K E] (c : E ≃ₐ[ℚ] E) (𝔟 : Ideal (𝓞 E))
    (h : differentIdeal (𝓞 K) (𝓞 E) = 𝔟 * (c • 𝔟)) :
    FractionalIdeal.absNorm (((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ *
        ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ^ 2 =
      (Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) : ℚ) := by
  have hD : differentIdeal (𝓞 K) (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hb : 𝔟 ≠ ⊥ := by
    rintro rfl
    exact hD (by rw [h]; exact Submodule.bot_mul _)
  have hcoe : ∀ J : Ideal (𝓞 E), FractionalIdeal.absNorm
      ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) = (Ideal.absNorm J : ℚ) := fun J =>
    FractionalIdeal.coeIdeal_absNorm J
  have hB : ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  rw [h, FractionalIdeal.coeIdeal_mul, ← mul_assoc, inv_mul_cancel₀ hB, one_mul, hcoe, map_mul,
    absNorm_galois_smul' E c 𝔟]
  push_cast
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem natAbs_discr_eq (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
    [Algebra K E] (d : ℕ) (hdK : NumberField.discr K = -(d : ℤ)) :
    (NumberField.discr E).natAbs =
      Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) * d ^ Module.finrank K E := by
  rw [← absNorm_differentIdeal E (𝓞 E),
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 E), map_mul,
    Ideal.absNorm_algebraMap, absNorm_differentIdeal K (𝓞 K), hdK,
    ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E]
  simp

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
