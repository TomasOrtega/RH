import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

/- English proof (translation)
Set `L` to `AlgebraicClosure K`. Set `f : (E →+* K) → (E →ₐ[ℚ] L)` to `fun σ => ((algebraMap K L).comp σ).toRatAlgHom`. Establish `hinj : Function.Injective f`. Introduce `σ τ hst`. Use extensionality with `x`.

Apply `(algebraMap K L).injective` to reduce the goal to its premises. Use `DFunLike.congr_fun hst x` as an intermediate fact. Simplify `this` using `[f]`. Establish `hbij : Function.Bijective f`. Rewrite using `[Fintype.bijective_iff_injective_and_card]`.

Use `⟨hinj, ?_⟩` and prove the remaining obligations. Rewrite using `[h, AlgHom.card]`. Apply `(algebraMap K L).injective` to reduce the goal to its premises. Establish `ht` using `trace_eq_sum_embeddings L (K := ℚ) (L := E) (x := y)`. Rewrite using `[map_sum, map_ratCast, ← eq_ratCast (algebraMap ℚ L), ht]`.

Conclude with `Fintype.sum_bijective f hbij _ _ (fun σ => by simp [f])`.
-/
theorem projSum_sum_embeddings_eq_trace (K : Type) [Field K] [CharZero K] (E : Type) [Field E]
    [NumberField E] [Fintype (E →+* K)] (h : Fintype.card (E →+* K) = Module.finrank ℚ E) (y : E) :
    ∑ σ : E →+* K, σ y = ((Algebra.trace ℚ E y : ℚ) : K) := by
  classical
  let L := AlgebraicClosure K
  let f : (E →+* K) → (E →ₐ[ℚ] L) := fun σ => ((algebraMap K L).comp σ).toRatAlgHom
  have hinj : Function.Injective f := by
    intro σ τ hst
    ext x
    apply (algebraMap K L).injective
    have := DFunLike.congr_fun hst x
    simpa [f] using this
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [h, AlgHom.card]
  apply (algebraMap K L).injective
  have ht := trace_eq_sum_embeddings L (K := ℚ) (L := E) (x := y)
  rw [map_sum, map_ratCast, ← eq_ratCast (algebraMap ℚ L), ht]
  exact Fintype.sum_bijective f hbij _ _ (fun σ => by simp [f])

/- English proof (translation)
Establish `h1 : (1 : E) = ∑ j, (((RingOfIntegers.basis E).repr 1 j : ℤ) : ℚ) • integralBasis E j`. Use `congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr 1)` as an intermediate fact. Rewrite `this` using `[map_sum, (algebraMap (𝓞 E) E).map_one]`. Use `this.symm.trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[integralBasis_apply, map_zsmul, Int.cast_smul_eq_zsmul]`. Establish `h2 : Algebra.trace ℚ E (dualInt E k) = Algebra.traceForm ℚ E (dualInt E k) 1`. Rewrite using `[Algebra.traceForm_apply, mul_one]`. Rewrite using `[h2]`. Use `conv_lhs => rw [h1]`.

Rewrite using `[map_sum]`. Simplify using `only [map_smul, dualInt, LinearMap.BilinForm.apply_dualBasis_left]`. Simplify using the standard rewrite rules.
-/
theorem projSum_trace_dualInt (E : Type) [Field E] [NumberField E]
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (dualInt E k) = (((RingOfIntegers.basis E).repr 1 k : ℤ) : ℚ) := by
  classical
  have h1 : (1 : E) = ∑ j, (((RingOfIntegers.basis E).repr 1 j : ℤ) : ℚ) • integralBasis E j := by
    have := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr 1)
    rw [map_sum, (algebraMap (𝓞 E) E).map_one] at this
    refine this.symm.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integralBasis_apply, map_zsmul, Int.cast_smul_eq_zsmul]
  have h2 : Algebra.trace ℚ E (dualInt E k) = Algebra.traceForm ℚ E (dualInt E k) 1 := by
    rw [Algebra.traceForm_apply, mul_one]
  rw [h2]
  conv_lhs => rw [h1]
  rw [map_sum]
  simp only [map_smul, dualInt, LinearMap.BilinForm.apply_dualBasis_left]
  simp

/- English proof (translation)
Unfold `eigProj`. Rewrite using `[Finset.sum_comm]`. Use `congrArg ρ ((RingOfIntegers.basis E).sum_repr 1)` as an intermediate fact. Rewrite `this` using `[map_sum, ρ.map_one]`. Use `Eq.trans ?_ this` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul, projSum_sum_embeddings_eq_trace K E h, projSum_trace_dualInt, Rat.cast_intCast, map_zsmul, Int.cast_smul_eq_zsmul]`.
-/
theorem sum_eigProj_eq_one (K : Type) [Field K] [CharZero K] (V : Type) [AddCommGroup V]
    [Module K V] (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V)
    [Fintype (E →+* K)] (h : Fintype.card (E →+* K) = Module.finrank ℚ E) :
    ∑ σ : E →+* K, eigProj ρ σ = 1 := by
  classical
  unfold eigProj
  rw [Finset.sum_comm]
  have := congrArg ρ ((RingOfIntegers.basis E).sum_repr 1)
  rw [map_sum, ρ.map_one] at this
  refine Eq.trans ?_ this
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul, projSum_sum_embeddings_eq_trace K E h, projSum_trace_dualInt,
    Rat.cast_intCast, map_zsmul, Int.cast_smul_eq_zsmul]

end GlobalTheory.CompanionTheory.Ar.HT
