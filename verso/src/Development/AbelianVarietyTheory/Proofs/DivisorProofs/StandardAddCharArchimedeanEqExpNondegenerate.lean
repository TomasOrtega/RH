import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.StdBeta

/- English proof (translation)
Introduce `u hu`. Establish `h : u.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u.1 * _ = 0`. Rewrite using `[h, zero_mul]`.

Conclude with `mul_zero u.2`.
-/
theorem at_arch (F : Type) [Field F] [NumberField F] (a : mixedEmbedding.mixedSpace F) :
    At (M := AF F) (evI F) (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) := by
  intro u hu
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · exact mul_zero u.2

/- English proof (translation)
The claim follows from `(InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a`.
-/
theorem evI_arch (F : Type) [Field F] [NumberField F] (a : mixedEmbedding.mixedSpace F) :
    evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) = a :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a

/- English proof (translation)
Introduce `F _ _ ψ hψ`. Use `⟨-(Algebra.trace ℝ (mixedEmbedding.mixedSpace F)), fun a => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[hψ.2.2 _ (at_arch F a), evI_arch]`. Simplify using `only [LinearMap.neg_apply, Complex.ofReal_neg]`. Put the polynomial expressions in normal form.

Assume the negation of the conclusion as `h push_neg at h`. Conclude with `ha (GlobalTheory.ArchUniq.Coord.eq_zero_of_trace a fun b => by`. Use `h b` as an intermediate fact. Rewrite `this` using `[LinearMap.neg_apply, neg_eq_zero]`. Conclude with `this)`.
-/
theorem stdBeta : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∃ β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ,
      (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
        Complex.exp (2 * Real.pi * Complex.I * β a)) ∧ ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0 := by
  intro F _ _ ψ hψ
  refine ⟨-(Algebra.trace ℝ (mixedEmbedding.mixedSpace F)), fun a => ?_, fun a ha => ?_⟩
  · rw [hψ.2.2 _ (at_arch F a), evI_arch]
    simp only [LinearMap.neg_apply, Complex.ofReal_neg]
    ring_nf
  · by_contra h
    push_neg at h
    exact ha (GlobalTheory.ArchUniq.Coord.eq_zero_of_trace a fun b => by
      have := h b
      rw [LinearMap.neg_apply, neg_eq_zero] at this
      exact this)

end GlobalTheory.StdBeta

end
