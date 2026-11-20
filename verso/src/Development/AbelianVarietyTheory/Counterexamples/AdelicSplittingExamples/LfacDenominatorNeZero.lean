import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke

noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn

namespace GlobalTheory.HeckeObjectExamples

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Introduce `hσ`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Use `h.2.1` as an intermediate fact. Apply `IsTotallyComplex.complexEmbedding_not_isReal τ` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Use `h.2.2.2 τ x` as an intermediate fact. Rewrite `this` using `[hσ]`. Simplify `this.symm` using `[ComplexEmbedding.conjugate_coe_eq]`.
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
Take `⟨α, rfl, h1, h0⟩` from `h`. Establish `: α * α = α`. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `w`. Express the relevant statement in the definitionally equal form `evalV F w (α * α) = evalV F w α`.

Rewrite using `[map_mul]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[h1, one_mul]`. Rewrite using `[h0 w hw, mul_zero]`.

Express the relevant statement in the definitionally equal form `((0 : Ainf F) * 0, α * α) = ((0 : Ainf F), α)`. Rewrite using `[this, mul_zero]`.
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
Break down `h with h | ⟨-, ⟨v, ε, hε, rfl⟩, -⟩` into its components or cases. Conclude with `h.1.1.1`. Rewrite using `[← map_mul, placeIdem_mul_self hε]`.
-/
theorem idem_mul_self {σ : E →ₐ[F] E} {P : HeightOneSpectrum (𝓞 E)} {e f : AE F E}
    (h : IsPrimeIdem σ P e f) : e * e = e := by
  rcases h with h | ⟨-, ⟨v, ε, hε, rfl⟩, -⟩
  · exact h.1.1.1
  · rw [← map_mul, placeIdem_mul_self hε]

/- English proof (translation)
Assemble the required witnesses or components as `⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _, fun τ x => IsCMField.complexEmbedding_complexConj K τ x⟩`.
-/
theorem isCMExt_of_isCMField (K : Type) [Field K] [NumberField K] [IsCMField K] :
    IsCMExt (maximalRealSubfield K) K (IsCMField.complexConj K).toAlgHom :=
  ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
    fun τ x => IsCMField.complexEmbedding_complexConj K τ x⟩

end GlobalTheory.HeckeObjectExamples
end
