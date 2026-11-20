import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermOne

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
  have hreal : w.IsReal := by
    rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
      NumberField.ComplexEmbedding.isReal_iff]
    refine RingHom.ext fun x ↦ ?_
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    change star (w.embedding x) = w.embedding x
    rw [← h.2.2.2, hc]
  exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Take a linear combination of the given relations to obtain the conclusion. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.

A detailed English derivation is pending.
-/
theorem exists_eq_algebraMap (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    ∃ β : F, x = algebraMap F E β := by
  by_contra hc
  push_neg at hc
  have hli : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have ht : t = 0 := by
      by_contra ht
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
      apply hc (-(s / t))
      rw [map_neg, map_div₀]
      field_simp
      linear_combination hst
    refine ⟨?_, ht⟩
    rw [ht, map_zero, zero_mul, add_zero] at hst
    exact (map_eq_zero_iff _ (algebraMap F E).injective).1 hst
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by
    rw [Fintype.card_fin, h.2.2.1]
  obtain ⟨y, hy⟩ := exists_ne h
  have hid : σ.toLinearMap = LinearMap.id := by
    refine (basisOfLinearIndependentOfCardEqFinrank hli hcard).ext fun i ↦ ?_
    fin_cases i <;> simp [hx]
  exact hy (by simpa using LinearMap.congr_fun hid y)

end GlobalTheory.CompanionTheory.SW.HermOne

namespace GlobalTheory.CompanionTheory.SW

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem hermOne_eq_scal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b), ∃ β : F, T = (fun _ _ => algebraMap F E β) ∧ (T.det ≠ 0 → β ≠ 0) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], hermOf R σ T hT = hermScal R σ (algebraMap F R β) := by
  intro F E _ _ _ _ _ σ h T hT
  obtain ⟨β, hβ⟩ := HermOne.exists_eq_algebraMap h (hT 0 0)
  have hTβ : T = fun _ _ => algebraMap F E β := by
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    exact hβ
  refine ⟨β, hTβ, fun hd hb => hd ?_, fun R _ _ => ?_⟩
  · rw [Matrix.det_fin_one, hβ, hb, map_zero]
  · apply Subtype.ext
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    change inclR R (T 0 0) = (algebraMap F R β) ⊗ₜ[F] (1 : E)
    rw [hβ, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp [inclR, TensorProduct.smul_tmul]

end GlobalTheory.CompanionTheory.SW
