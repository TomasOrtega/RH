import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory.HeckeSplit

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem exists_int_moved (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (hc : c ≠ 1) : ∃ θ : 𝓞 E, c (θ : E) ≠ (θ : E) := by
  by_contra h
  push_neg at h
  apply hc
  ext z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) z
  simp only [map_div₀, AlgEquiv.one_apply]
  exact congrArg₂ (· / ·) (h a) (h b)

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finite_setOf_mem_asIdeal (E : Type) [Field E] [NumberField E] (δ : 𝓞 E) (h : δ ≠ 0) :
    {w : HeightOneSpectrum (𝓞 E) | δ ∈ w.asIdeal}.Finite := by
  have := Ideal.finite_factors (R := 𝓞 E) (I := Ideal.span {δ}) (by simpa using h)
  refine this.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hw

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem eventually_degOne_moved : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Algebra.IsQuadraticExtension F E] (c : E ≃ₐ[F] E), c ≠ 1 →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, DegOne F w →
      ∃ x : 𝓞 E, x ∈ w.asIdeal ∧ ∀ y : 𝓞 E, (y : E) = c (x : E) → y ∉ w.asIdeal := by
  intro F E _ _ _ _ _ _ c hc
  obtain ⟨θ, hθ⟩ := exists_int_moved F E c hc
  have hint : IsIntegral ℤ (c (θ : E)) := θ.isIntegral_coe.map c.toRingHom.toIntAlgHom
  set θ' : 𝓞 E := ⟨c (θ : E), hint⟩ with hθ'
  have hδ : θ - θ' ≠ 0 := by
    intro h0
    apply hθ
    have := congrArg (fun t : 𝓞 E => (t : E)) h0
    push_cast at this
    exact (sub_eq_zero.mp this).symm
  refine (finite_setOf_mem_asIdeal E (θ - θ') hδ).subset ?_ |> Filter.eventually_cofinite.mpr
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hnot
  apply hw
  intro hdeg
  obtain ⟨u, hu⟩ := hdeg θ
  refine ⟨θ - algebraMap (𝓞 F) (𝓞 E) u, hu, fun y hy hyw => hnot ?_⟩
  have hcu : c ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) = ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) := by
    have : ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) = algebraMap F E (u : F) := rfl
    rw [this, AlgEquiv.commutes]
  have hy' : y = θ' - algebraMap (𝓞 F) (𝓞 E) u := by
    apply RingOfIntegers.ext
    rw [hy]
    push_cast
    rw [map_sub, hcu]
    rfl
  have := w.asIdeal.sub_mem hu hyw
  rw [hy'] at this
  convert this using 1
  ring

end GlobalTheory.HeckeSplit
