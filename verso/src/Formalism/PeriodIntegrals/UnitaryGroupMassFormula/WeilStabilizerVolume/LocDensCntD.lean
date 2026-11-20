import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.UnifVSpec

noncomputable section

namespace PI.VolStabW

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hinv` using `sigma_invol σ hCM.2.2.2`. Establish `hne : ∃ e, σ e ≠ e`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Set `w : InfinitePlace E` to `Classical.arbitrary _`.

Establish `hc : w.IsComplex` using `hCM.2.1.isComplex w`. Apply `(InfinitePlace.not_isReal_iff_isComplex.2 hc)` to reduce the goal to its premises. Rewrite using `[InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Use `hCM.2.2.2 w.embedding x` as an intermediate fact.

Rewrite `this` using `[h x]`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply]`. Conclude with `this.symm`. Take `⟨e, he⟩` from `hne`. Use `⟨e - σ e, sub_ne_zero.2 (Ne.symm he), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, hinv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_anti (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  have hinv := sigma_invol σ hCM.2.2.2
  have hne : ∃ e, σ e ≠ e := by
    by_contra h
    push Not at h
    let w : InfinitePlace E := Classical.arbitrary _
    have hc : w.IsComplex := hCM.2.1.isComplex w
    apply (InfinitePlace.not_isReal_iff_isComplex.2 hc)
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    have := hCM.2.2.2 w.embedding x
    rw [h x] at this
    rw [ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply]
    exact this.symm
  obtain ⟨e, he⟩ := hne
  refine ⟨e - σ e, sub_ne_zero.2 (Ne.symm he), ?_⟩
  rw [map_sub, hinv]; ring

/- English proof (translation)
Simplify using `only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, hσδ, mul_one] at h`. Establish `h2 : (2 : E) * (algebraMap F E t * δ) = 0` using `by linear_combination -h`. Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `absurd h3 two_ne_zero`. Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases.

Conclude with `(algebraMap F E).injective (by rw [h4, map_zero])`. Conclude with `absurd h4 hδ0`.
-/
theorem anti_coeff (σ : E →ₐ[F] E) {δ : E} (hδ0 : δ ≠ 0) (hσδ : σ δ = -δ) (s t : F)
    (h : σ (s • (1 : E) + t • δ) = s • 1 + t • δ) : t = 0 := by
  simp only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, hσδ, mul_one] at h
  have h2 : (2 : E) * (algebraMap F E t * δ) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact (algebraMap F E).injective (by rw [h4, map_zero])
    · exact absurd h4 hδ0

/- English proof (translation)
Take `⟨δ, hδ0, hσδ⟩` from `exists_anti σ hCM`. Establish `hinv` using `sigma_invol σ hCM.2.2.2`. Establish `li : LinearIndependent F ![(1 : E), δ]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`.

Establish `ht : t = 0` using `anti_coeff σ hδ0 hσδ s t (by rw [hst, map_zero])`. Substitute `ht` using the available equality. Simplify using `only [zero_smul, add_zero] at hst`. Conclude with `⟨(smul_eq_zero.1 hst).resolve_right one_ne_zero, rfl⟩`. Establish `hcard : Fintype.card (Fin 2) = Module.finrank F E`.

Rewrite using `[hCM.2.2.1]`. Both sides reduce to the same expression. Set `c` to `basisOfLinearIndependentOfCardEqFinrank li hcard`. Establish `hc0 : c 0 = 1` using `by simp [c]`. Establish `hc1 : c 1 = δ` using `by simp [c]`.

Establish `hsum` using `c.sum_repr (δ * δ)`. Rewrite `hsum` using `[Fin.sum_univ_two, hc0, hc1]`. Establish `hβ : c.repr (δ * δ) 1 = 0`. Use `anti_coeff σ hδ0 hσδ (c.repr (δ * δ) 0) _ ?_` and prove the remaining obligations. Rewrite using `[hsum, map_mul, hσδ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hsum` using `[hβ, zero_smul, add_zero, Algebra.smul_def, mul_one]`. Use `⟨δ, c.repr (δ * δ) 0, c, hδ0, hσδ, hsum.symm, ?_, hc0, hc1⟩` and prove the remaining obligations. Introduce `h0`. Rewrite `hsum` using `[h0, map_zero]`.

Conclude with `hδ0 (mul_self_eq_zero.1 hsum.symm)`.
-/
theorem exists_basis_anti (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) :
    ∃ (δ : E) (D0 : F) (c : Module.Basis (Fin 2) F E), δ ≠ 0 ∧ σ δ = -δ ∧
      δ * δ = algebraMap F E D0 ∧ D0 ≠ 0 ∧ c 0 = 1 ∧ c 1 = δ := by
  obtain ⟨δ, hδ0, hσδ⟩ := exists_anti σ hCM
  have hinv := sigma_invol σ hCM.2.2.2
  have li : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := anti_coeff σ hδ0 hσδ s t (by rw [hst, map_zero])
    subst ht
    simp only [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right one_ne_zero, rfl⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by
    rw [hCM.2.2.1]; rfl
  let c := basisOfLinearIndependentOfCardEqFinrank li hcard
  have hc0 : c 0 = 1 := by simp [c]
  have hc1 : c 1 = δ := by simp [c]
  have hsum := c.sum_repr (δ * δ)
  rw [Fin.sum_univ_two, hc0, hc1] at hsum
  have hβ : c.repr (δ * δ) 1 = 0 := by
    refine anti_coeff σ hδ0 hσδ (c.repr (δ * δ) 0) _ ?_
    rw [hsum, map_mul, hσδ]; ring
  rw [hβ, zero_smul, add_zero, Algebra.smul_def, mul_one] at hsum
  refine ⟨δ, c.repr (δ * δ) 0, c, hδ0, hσδ, hsum.symm, ?_, hc0, hc1⟩
  intro h0
  rw [h0, map_zero] at hsum
  exact hδ0 (mul_self_eq_zero.1 hsum.symm)

end PI.VolStabW
