import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlace

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.InertDifferentGen

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `h1 : J⁻¹ * J = 1` using `inv_mul_cancel₀ hJ`. Establish `hone : (1 : E) ∈ J⁻¹ * J` using `by rw [h1]; exact FractionalIdeal.one_mem_one _`. Establish `key : w.valuation E (1 : E) < 1`.

Use `FractionalIdeal.mul_induction_on (C := fun x => w.valuation E x < 1) hone ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`. Establish `hm : a * b ∈ J⁻¹ * J` using `FractionalIdeal.mul_mem_mul ha hb`. Rewrite `hm` using `[h1, FractionalIdeal.mem_one_iff]`. Take `⟨x, hx⟩` from `hm`.

Use `lt_of_le_of_ne ?_ (h a ha b hb)` and prove the remaining obligations. Rewrite using `[← hx]`. Conclude with `w.valuation_le_one x`. Introduce `x y hx hy`. Conclude with `Valuation.map_add_lt _ hx hy`.

Simplify using `at key`.
-/
theorem exists_mul_valuation_eq_one {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : J ≠ 0) :
    ∃ δ ∈ J⁻¹, ∃ z ∈ J, w.valuation E (δ * z) = 1 := by
  by_contra h
  push Not at h
  have h1 : J⁻¹ * J = 1 := inv_mul_cancel₀ hJ
  have hone : (1 : E) ∈ J⁻¹ * J := by rw [h1]; exact FractionalIdeal.one_mem_one _
  have key : w.valuation E (1 : E) < 1 := by
    refine FractionalIdeal.mul_induction_on (C := fun x => w.valuation E x < 1) hone ?_ ?_
    · intro a ha b hb
      have hm : a * b ∈ J⁻¹ * J := FractionalIdeal.mul_mem_mul ha hb
      rw [h1, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨x, hx⟩ := hm
      refine lt_of_le_of_ne ?_ (h a ha b hb)
      rw [← hx]
      exact w.valuation_le_one x
    · intro x y hx hy
      exact Valuation.map_add_lt _ hx hy
  simp at key

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (𝓞 E)⁰ E))]`. Prove the components needed by the constructor for the conclusion. Introduce `h o`. Take `⟨k, hk⟩` from `h (o : E) ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)`. Rewrite `hk` using `[Algebra.traceForm_apply, mul_comm]`.

Rewrite using `[← hk]`. Conclude with `isIntegral_algebraMap`. Introduce `h a ha`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Take `⟨k, hk⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (h o)`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.traceForm_apply, mul_comm]`. Conclude with `hk`.
-/
theorem mem_dual_one_iff {E : Type} [Field E] [NumberField E] (e : E) :
    e ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e)) := by
  rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (𝓞 E)⁰ E))]
  constructor
  · intro h o
    obtain ⟨k, hk⟩ := h (o : E) ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply, mul_comm] at hk
    rw [← hk]
    exact isIntegral_algebraMap
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h o)
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, mul_comm]
    exact hk

/- English proof (translation)
Introduce `F E _ _ _ _ _ v w hin`. Establish `hJ : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero`. Take `⟨δ, hδ, z, hz, hδz⟩` from `exists_mul_valuation_eq_one w _ hJ`. Take `⟨t, ht⟩` from `v.valuation_surjective F (w.valuation E δ)`. Rewrite `ht` using `[← GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt F E v w hin]`.

Establish `hδ0 : w.valuation E δ ≠ 0`. Introduce `h0`. Rewrite `hδz` using `[map_mul, h0, zero_mul]`. Conclude with `zero_ne_one hδz`. Establish `htE : algebraMap F E t ≠ 0`.

Introduce `h0`. Rewrite `ht` using `[h0, map_zero]`. Conclude with `hδ0 ht.symm`. Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`.

Conclude with `htE (map_zero _)`. Use `⟨t, ht0, δ / algebraMap F E t, algebraMap F E t * z, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, ht, div_self hδ0]`. Rewrite using `[map_mul, ht, ← map_mul, hδz]`. Introduce `e he`.

Rewrite using `[div_mul_cancel₀ _ htE]`. Establish `hm` using `FractionalIdeal.mul_mem_mul hδ ((mem_dual_one_iff e).2 he)`. Rewrite `hm` using `[inv_mul_cancel₀ hJ, FractionalIdeal.mem_one_iff]`. Conclude with `hm`. Rewrite using `[mul_comm (algebraMap F E t) z, mul_inv_cancel_right₀ htE]`.

Conclude with `(mem_dual_one_iff z).1 hz`.
-/
theorem exists_generator_different_of_isInertAt :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∃ t : F, t ≠ 0 ∧ ∃ s₁ s₂ : E, w.valuation E s₁ = 1 ∧ w.valuation E s₂ = 1 ∧
    (∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) →
      s₁ * algebraMap F E t * e ∈ (algebraMap (𝓞 E) E).range) ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (s₂ * (algebraMap F E t)⁻¹)))) := by
  intro F E _ _ _ _ _ v w hin
  have hJ : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  obtain ⟨δ, hδ, z, hz, hδz⟩ := exists_mul_valuation_eq_one w _ hJ
  obtain ⟨t, ht⟩ := v.valuation_surjective F (w.valuation E δ)
  rw [← GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt F E v w hin] at ht
  have hδ0 : w.valuation E δ ≠ 0 := by
    intro h0
    rw [map_mul, h0, zero_mul] at hδz
    exact zero_ne_one hδz
  have htE : algebraMap F E t ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ht
    exact hδ0 ht.symm
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact htE (map_zero _)
  refine ⟨t, ht0, δ / algebraMap F E t, algebraMap F E t * z, ?_, ?_, ?_, ?_⟩
  · rw [map_div₀, ht, div_self hδ0]
  · rw [map_mul, ht, ← map_mul, hδz]
  · intro e he
    rw [div_mul_cancel₀ _ htE]
    have hm := FractionalIdeal.mul_mem_mul hδ ((mem_dual_one_iff e).2 he)
    rw [inv_mul_cancel₀ hJ, FractionalIdeal.mem_one_iff] at hm
    exact hm
  · rw [mul_comm (algebraMap F E t) z, mul_inv_cancel_right₀ htE]
    exact (mem_dual_one_iff z).1 hz

end GlobalTheory.InertDifferentGen
