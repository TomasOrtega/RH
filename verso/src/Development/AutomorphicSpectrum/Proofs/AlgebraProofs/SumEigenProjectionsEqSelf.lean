import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig

/- English proof (translation)
Set `Ω` to `AlgebraicClosure C`. Set `f : (E →+* C) → (E →ₐ[ℚ] Ω)` to `fun s => RingHom.toRatAlgHom ((algebraMap C Ω).comp s)`. Establish `hf : ∀ s y, f s y = algebraMap C Ω (s y)` using `fun s y => rfl`. Establish `hinj : Function.Injective f`. Introduce `s t hst`.

Use extensionality with `y`. Establish `h` using `congrArg (fun φ : E →ₐ[ℚ] Ω => φ y) hst`. Simplify using `only [hf] at h`. Conclude with `(algebraMap C Ω).injective h`. Establish `hbij : Function.Bijective f`.

Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Conclude with `⟨hinj, by rw [hc, AlgHom.card]⟩`. Establish `key : algebraMap ℚ Ω (Algebra.trace ℚ E x) = ∑ σ : E →ₐ[ℚ] Ω, σ x` using `trace_eq_sum_embeddings Ω (x := x)`. Rewrite `key` using `[← hbij.sum_comp (fun σ : E →ₐ[ℚ] Ω => σ x)]`. Simplify using `only [hf] at key`.

Apply `(algebraMap C Ω).injective` to reduce the goal to its premises. Rewrite using `[map_sum, ← key, eq_ratCast (algebraMap ℚ Ω), eq_ratCast (algebraMap ℚ C), map_ratCast]`.
-/
theorem sum_embeddings_eq_trace (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    [Fintype (E →+* C)] (hc : Fintype.card (E →+* C) = Module.finrank ℚ E) (x : E) :
    ∑ s : E →+* C, s x = algebraMap ℚ C (Algebra.trace ℚ E x) := by
  classical
  let Ω := AlgebraicClosure C
  let f : (E →+* C) → (E →ₐ[ℚ] Ω) := fun s => RingHom.toRatAlgHom ((algebraMap C Ω).comp s)
  have hf : ∀ s y, f s y = algebraMap C Ω (s y) := fun s y => rfl
  have hinj : Function.Injective f := by
    intro s t hst
    ext y
    have h := congrArg (fun φ : E →ₐ[ℚ] Ω => φ y) hst
    simp only [hf] at h
    exact (algebraMap C Ω).injective h
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [hc, AlgHom.card]⟩
  have key : algebraMap ℚ Ω (Algebra.trace ℚ E x) = ∑ σ : E →ₐ[ℚ] Ω, σ x :=
    trace_eq_sum_embeddings Ω (x := x)
  rw [← hbij.sum_comp (fun σ : E →ₐ[ℚ] Ω => σ x)] at key
  simp only [hf] at key
  apply (algebraMap C Ω).injective
  rw [map_sum, ← key, eq_ratCast (algebraMap ℚ Ω), eq_ratCast (algebraMap ℚ C), map_ratCast]

/- English proof (translation)
Use `set b := RingOfIntegers.basis E with hb`. Establish `h1 : (1 : E) = ∑ j, ((b.repr 1 j : ℤ) : ℚ) • integralBasis E j`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[integralBasis_apply, map_zsmul, Int.cast_smul_eq_zsmul]`. Establish `htr : ∀ k, Algebra.trace ℚ E (HT.dualInt E k) = ((b.repr 1 k : ℤ) : ℚ)`. Introduce `k`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Algebra.traceForm_apply, mul_one]`.

Use `_ = ∑ j, ((b.repr 1 j : ℤ) : ℚ) * Algebra.traceForm ℚ E (HT.dualInt E k) (integralBasis E j) := by conv_lhs => rw [h1]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul]`. Use `_ = ((b.repr 1 k : ℤ) : ℚ) := by`.

Simplify using `only [HT.dualInt, LinearMap.BilinForm.apply_dualBasis_left, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `hsum : ∀ k, ∑ s : E →+* C, s (HT.dualInt E k) = ((b.repr 1 k : ℤ) : C)`. Introduce `k`. Rewrite using `[sum_embeddings_eq_trace E C hc, htr, map_intCast]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [HT.eigProj]`. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, hb]`. Use `_ = ∑ k, (∑ s : E →+* C, s (HT.dualInt E k)) • ρ (b k) y := by`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`. Use `_ = ∑ k, ((b.repr 1 k : ℤ) : C) • ρ (b k) y := by`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hsum]`. Use `_ = ρ (∑ k, b.repr 1 k • b k) y := by`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]`.

Use `_ = y := by`. Rewrite using `[b.sum_repr, map_one, Module.End.one_apply]`.
-/
theorem sum_eigProj (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    [Fintype (E →+* C)] (hc : Fintype.card (E →+* C) = Module.finrank ℚ E)
    (M : Type) [AddCommGroup M] [Module C M] (ρ : 𝓞 E →+* Module.End C M) (y : M) :
    ∑ s, HT.eigProj ρ s y = y := by
  classical
  set b := RingOfIntegers.basis E with hb
  have h1 : (1 : E) = ∑ j, ((b.repr 1 j : ℤ) : ℚ) • integralBasis E j := by
    calc (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
      _ = algebraMap (𝓞 E) E (∑ j, b.repr 1 j • b j) := by rw [b.sum_repr]
      _ = ∑ j, ((b.repr 1 j : ℤ) : ℚ) • integralBasis E j := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integralBasis_apply, map_zsmul, Int.cast_smul_eq_zsmul]
  have htr : ∀ k, Algebra.trace ℚ E (HT.dualInt E k) = ((b.repr 1 k : ℤ) : ℚ) := by
    intro k
    calc Algebra.trace ℚ E (HT.dualInt E k) = Algebra.traceForm ℚ E (HT.dualInt E k) 1 := by
          rw [Algebra.traceForm_apply, mul_one]
      _ = ∑ j, ((b.repr 1 j : ℤ) : ℚ) * Algebra.traceForm ℚ E (HT.dualInt E k) (integralBasis E j) := by
          conv_lhs => rw [h1]
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, smul_eq_mul]
      _ = ((b.repr 1 k : ℤ) : ℚ) := by
          simp only [HT.dualInt, LinearMap.BilinForm.apply_dualBasis_left, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsum : ∀ k, ∑ s : E →+* C, s (HT.dualInt E k) = ((b.repr 1 k : ℤ) : C) := by
    intro k
    rw [sum_embeddings_eq_trace E C hc, htr, map_intCast]
  calc ∑ s, HT.eigProj ρ s y = ∑ s : E →+* C, ∑ k, s (HT.dualInt E k) • ρ (b k) y := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [HT.eigProj]
        rw [LinearMap.sum_apply]
        simp only [LinearMap.smul_apply, hb]
    _ = ∑ k, (∑ s : E →+* C, s (HT.dualInt E k)) • ρ (b k) y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ k, ((b.repr 1 k : ℤ) : C) • ρ (b k) y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hsum]
    _ = ρ (∑ k, b.repr 1 k • b k) y := by
        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
    _ = y := by
        rw [b.sum_repr, map_one, Module.End.one_apply]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig
