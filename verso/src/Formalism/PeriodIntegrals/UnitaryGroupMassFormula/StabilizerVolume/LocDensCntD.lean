import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnifVSpec

noncomputable section

namespace PI.VolStabS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨_, hE, _, hτ⟩` from `hCM`. Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom`. Establish `hinv : ∀ x, σ (σ x) = x`. Introduce `x`. Apply `τ.injective` to reduce the goal to its premises.

Rewrite using `[hτ, hτ, star_star]`. Establish `hne : ∃ x, σ x ≠ x`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Use `haveI := hE`.

Establish `hc` using `IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk τ)`. Rewrite `hc` using `[NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff]`. Apply `hc` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← hτ, hall]`.

Take `⟨x, hx⟩` from `hne`. Use `⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hinv]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_anti (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨_, hE, _, hτ⟩ := hCM
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hτ, hτ, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    haveI := hE
    have hc := IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk τ)
    rw [NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff] at hc
    apply hc
    ext x
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← hτ, hall]
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv]
  abel

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
Take `⟨δ, hδ0, hσδ⟩` from `exists_anti σ hCM`. Establish `h2 : Module.finrank F E = 2` using `hCM.2.2.1`. Establish `hli : LinearIndependent F ![(1 : E), δ]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`.

Establish `ht : t = 0`. Apply `anti_coeff σ hδ0 hσδ s t` to reduce the goal to its premises. Rewrite using `[hst, map_zero]`. Substitute `ht` using the available equality. Rewrite `hst` using `[zero_smul, add_zero, smul_eq_zero]`.

Conclude with `⟨hst.resolve_right one_ne_zero, rfl⟩`. Set `c` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])`. Establish `hc : ⇑c = ![(1 : E), δ]` using `coe_basisOfLinearIndependentOfCardEqFinrank hli _`. Choose the witnesses or unpack the hypotheses as in `⟨s, t, hst⟩ : ∃ s t : F, δ * δ = s • (1 : E) + t • δ := by`. Establish `hsum` using `c.sum_repr (δ * δ)`.

Rewrite `hsum` using `[Fin.sum_univ_two, hc]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one] at hsum`. Conclude with `⟨_, _, hsum.symm⟩`. Establish `ht : t = 0`. Apply `anti_coeff σ hδ0 hσδ s t` to reduce the goal to its premises.

Rewrite using `[← hst, map_mul, hσδ, neg_mul_neg]`. Substitute `ht` using the available equality. Rewrite `hst` using `[zero_smul, add_zero, Algebra.smul_def, mul_one]`. Use `⟨δ, s, c, hδ0, hσδ, hst, ?_, by simp [hc], by simp [hc]⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Rewrite `hst` using `[map_zero]`. Conclude with `hδ0 (mul_self_eq_zero.mp hst)`.
-/
theorem exists_basis_anti (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) :
    ∃ (δ : E) (D0 : F) (c : Module.Basis (Fin 2) F E), δ ≠ 0 ∧ σ δ = -δ ∧
      δ * δ = algebraMap F E D0 ∧ D0 ≠ 0 ∧ c 0 = 1 ∧ c 1 = δ := by
  obtain ⟨δ, hδ0, hσδ⟩ := exists_anti σ hCM
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      apply anti_coeff σ hδ0 hσδ s t
      rw [hst, map_zero]
    subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right one_ne_zero, rfl⟩
  let c := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hc : ⇑c = ![(1 : E), δ] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  obtain ⟨s, t, hst⟩ : ∃ s t : F, δ * δ = s • (1 : E) + t • δ := by
    have hsum := c.sum_repr (δ * δ)
    rw [Fin.sum_univ_two, hc] at hsum
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hsum
    exact ⟨_, _, hsum.symm⟩
  have ht : t = 0 := by
    apply anti_coeff σ hδ0 hσδ s t
    rw [← hst, map_mul, hσδ, neg_mul_neg]
  subst ht
  rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
  refine ⟨δ, s, c, hδ0, hσδ, hst, ?_, by simp [hc], by simp [hc]⟩
  rintro rfl
  rw [map_zero] at hst
  exact hδ0 (mul_self_eq_zero.mp hst)

end PI.VolStabS
