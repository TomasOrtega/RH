import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke

noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn

namespace GlobalTheory.HeckeObjectExamples

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem sigma_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := h.2.1
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem placeIdem_mul_self {v : HeightOneSpectrum (𝓞 F)} {ε : AF F}
    (h : IsPlaceIdem F v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have : α * α = α := by
    apply RestrictedProduct.ext
    intro w
    change evalV F w (α * α) = evalV F w α
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [h1, one_mul]
    · rw [h0 w hw, mul_zero]
  change ((0 : Ainf F) * 0, α * α) = ((0 : Ainf F), α)
  rw [this, mul_zero]

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem idem_mul_self {σ : E →ₐ[F] E} {P : HeightOneSpectrum (𝓞 E)} {e f : AE F E}
    (h : IsPrimeIdem σ P e f) : e * e = e := by
  rcases h with h | ⟨-, ⟨v, ε, hε, rfl⟩, -⟩
  · exact h.1.1.1
  · rw [← map_mul, placeIdem_mul_self hε]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isCMExt_of_isCMField (K : Type) [Field K] [NumberField K] [IsCMField K] :
    IsCMExt (maximalRealSubfield K) K (IsCMField.complexConj K).toAlgHom :=
  ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
    fun τ x => IsCMField.complexEmbedding_complexConj K τ x⟩

end GlobalTheory.HeckeObjectExamples
end
