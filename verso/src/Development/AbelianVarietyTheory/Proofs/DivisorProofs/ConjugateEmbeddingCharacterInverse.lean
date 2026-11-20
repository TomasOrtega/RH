import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.NuConjInv
open scoped TensorProduct
open GlobalTheory.KSplit

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2 τ, h.2.2.2 τ, star_star]`.
-/
theorem conj_conj (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hfix : ∀ x, σ x = x` using `fun x => by`. Assume the negation of the conclusion as `hne`. Conclude with `hc (x - σ x) (sub_ne_zero.mpr (Ne.symm hne)) (by rw [map_sub, conj_conj h]; ring)`.

Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hreal : ComplexEmbedding.IsReal τ`. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`.

Use `h.2.2.2 τ x` as an intermediate fact. Rewrite `this` using `[hfix]`. Conclude with `this.symm`. Establish `hc'` using `h.2.1.isComplex (InfinitePlace.mk τ)`. Rewrite `hc'` using `[← InfinitePlace.not_isReal_iff_isComplex]`.

Conclude with `hc' (InfinitePlace.isReal_mk_iff.mpr hreal)`.
-/
theorem exists_anti (h : IsCMExt F E σ) : ∃ ξ : E, ξ ≠ 0 ∧ σ ξ = -ξ := by
  by_contra hc
  push_neg at hc
  have hfix : ∀ x, σ x = x := fun x => by
    by_contra hne
    exact hc (x - σ x) (sub_ne_zero.mpr (Ne.symm hne)) (by rw [map_sub, conj_conj h]; ring)
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 τ x
    rw [hfix] at this
    exact this.symm
  have hc' := h.2.1.isComplex (InfinitePlace.mk τ)
  rw [← InfinitePlace.not_isReal_iff_isComplex] at hc'
  exact hc' (InfinitePlace.isReal_mk_iff.mpr hreal)

/- English proof (translation)
Take `⟨ξ, hξ0, hξ⟩` from `exists_anti h`. Establish `hli : LinearIndependent F ![(1 : E), ξ]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s u hsu`. Simplify using `only [Algebra.smul_def, mul_one] at hsu`.

Establish `h2` using `congrArg σ hsu`. Simplify using `only [map_add, map_mul, AlgHom.commutes, hξ, map_zero] at h2`. Establish `h3 : algebraMap F E u * ξ = 0` using `by linear_combination (hsu - h2) / 2`. Establish `hu : u = 0` using `(map_eq_zero (algebraMap F E)).mp ((mul_eq_zero.mp h3).resolve_right hξ0)`. Substitute `hu` using the available equality.

Use `⟨(map_eq_zero (algebraMap F E)).mp (by simpa using hsu), rfl⟩` and prove the remaining obligations. Establish `hcard : Fintype.card (Fin 2) = Module.finrank F E` using `by rw [h.2.2.1]; rfl`. Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli hcard`. Establish `hb : ∀ i, b i = ![(1 : E), ξ] i` using `fun i => by simp [b]`. Use `⟨(1 : AF F) ⊗ₜ[F] ξ, ⟨?_, ?_, ⟨Algebra.TensorProduct.basis (AF F) b, ?_, ?_⟩⟩⟩` and prove the remaining obligations.

Apply the tactic sequence `refine ⟨⟨(1 : AF F) ⊗ₜ[F] ξ, (1 : AF F) ⊗ₜ[F] ξ⁻¹, ?_, ?_⟩, rfl⟩ <;>`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul, hξ0, ← Algebra.TensorProduct.one_def]`. Simplify using `[cA, Algebra.TensorProduct.map_tmul, hξ, TensorProduct.tmul_neg]`. Rewrite using `[Algebra.TensorProduct.basis_apply, hb]`. Both sides reduce to the same expression.

Rewrite using `[Algebra.TensorProduct.basis_apply, hb]`. Both sides reduce to the same expression.
-/
theorem exists_isQuad (h : IsCMExt F E σ) : ∃ ξ : AE F E, IsQuad (cA σ) ξ := by
  obtain ⟨ξ, hξ0, hξ⟩ := exists_anti h
  have hli : LinearIndependent F ![(1 : E), ξ] := by
    rw [LinearIndependent.pair_iff]
    intro s u hsu
    simp only [Algebra.smul_def, mul_one] at hsu
    have h2 := congrArg σ hsu
    simp only [map_add, map_mul, AlgHom.commutes, hξ, map_zero] at h2
    have h3 : algebraMap F E u * ξ = 0 := by linear_combination (hsu - h2) / 2
    have hu : u = 0 := (map_eq_zero (algebraMap F E)).mp ((mul_eq_zero.mp h3).resolve_right hξ0)
    subst hu
    refine ⟨(map_eq_zero (algebraMap F E)).mp (by simpa using hsu), rfl⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ i, b i = ![(1 : E), ξ] i := fun i => by simp [b]
  refine ⟨(1 : AF F) ⊗ₜ[F] ξ, ⟨?_, ?_, ⟨Algebra.TensorProduct.basis (AF F) b, ?_, ?_⟩⟩⟩
  · refine ⟨⟨(1 : AF F) ⊗ₜ[F] ξ, (1 : AF F) ⊗ₜ[F] ξ⁻¹, ?_, ?_⟩, rfl⟩ <;>
      simp [Algebra.TensorProduct.tmul_mul_tmul, hξ0, ← Algebra.TensorProduct.one_def]
  · simp [cA, Algebra.TensorProduct.map_tmul, hξ, TensorProduct.tmul_neg]
  · rw [Algebra.TensorProduct.basis_apply, hb]; rfl
  · rw [Algebra.TensorProduct.basis_apply, hb]; rfl

end Local

end GlobalTheory.NuConjInv
