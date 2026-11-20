import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h`. Take `⟨-, hC, h2, hconj⟩` from `h`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)`. Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Use `set τ : E →+* ℂ := w.embedding with hτ`.

Establish `hne : ∃ e : E, σ e ≠ e`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `hreal : ComplexEmbedding.IsReal τ`. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Use `hconj τ x` as an intermediate fact. Rewrite `this` using `[hall x]`. Simplify `this.symm` using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `(InfinitePlace.not_isReal_iff_isComplex.mpr (hC.isComplex w)) (InfinitePlace.isReal_iff.mpr hreal)`.

Establish `hinv : ∀ x, σ (σ x) = x`. Introduce `x`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hconj, hconj, star_star]`. Take `⟨e, he⟩` from `hne`.

Use `set ξ : E := e - σ e with hξ`. Establish `hξ0 : ξ ≠ 0` using `fun h0 => he (sub_eq_zero.mp h0).symm`. Establish `hσξ : σ ξ = -ξ`. Simplify using `only [hξ, map_sub, hinv, neg_sub]`. Establish `h2E : (2 : E) ≠ 0` using `two_ne_zero`.

Establish `hli : LinearIndependent F ![(1 : E), ξ]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Establish `hst' : algebraMap F E s + algebraMap F E t * ξ = 0`. Simplify `hst` using `[Algebra.smul_def]`.

Establish `hσ' : algebraMap F E s - algebraMap F E t * ξ = 0`. Use `congrArg σ hst'` as an intermediate fact. Simplify `this` using `[map_add, map_mul, AlgHom.commutes, hσξ, sub_eq_add_neg]`. Establish `hs : algebraMap F E s = 0`. Establish `: 2 * algebraMap F E s = 0` using `by linear_combination hst' + hσ'`.

Conclude with `(mul_eq_zero.mp this).resolve_left h2E`. Establish `ht : algebraMap F E t * ξ = 0`. Establish `: 2 * (algebraMap F E t * ξ) = 0` using `by linear_combination hst' - hσ'`. Conclude with `(mul_eq_zero.mp this).resolve_left h2E`. Use `⟨(map_eq_zero _).mp hs, (map_eq_zero _).mp ((mul_eq_zero.mp ht).resolve_right hξ0)⟩` and prove the remaining obligations.

Establish `hspan` using `hli.span_eq_top_of_card_eq_finrank' (by simp [h2])`. Establish `hmem : ξ ^ 2 ∈ Submodule.span F (Set.range ![(1 : E), ξ])`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun F).mp hmem`.

Rewrite `hc` using `[Fin.sum_univ_two]`. Establish `hc' : algebraMap F E (c 0) + algebraMap F E (c 1) * ξ = ξ ^ 2`. Simplify `hc` using `[Algebra.smul_def]`. Establish `hc'' : algebraMap F E (c 0) - algebraMap F E (c 1) * ξ = ξ ^ 2`. Use `congrArg σ hc'` as an intermediate fact.

Simplify `this` using `[map_add, map_mul, map_pow, AlgHom.commutes, hσξ, sub_eq_add_neg]`. Establish `hb : algebraMap F E (c 1) * ξ = 0`. Establish `: 2 * (algebraMap F E (c 1) * ξ) = 0` using `by linear_combination hc' - hc''`. Conclude with `(mul_eq_zero.mp this).resolve_left h2E`. Establish `hsq : ξ ^ 2 = algebraMap F E (c 0)`.

Rewrite using `[← hc', hb, add_zero]`. Use `⟨c 0, ?_, ξ, hsq, hσξ⟩` and prove the remaining obligations. Introduce `r hr`. Establish `hfix : ∀ x : F, σ (algebraMap F E x) = algebraMap F E x` using `σ.commutes`. Establish `hprod : (ξ - algebraMap F E r) * (ξ + algebraMap F E r) = 0`.

Establish `: algebraMap F E (c 0) = algebraMap F E r ^ 2` using `by rw [← hr, map_pow]`. Take the linear combination `hsq + this`. Establish `hcontra : ξ = -ξ`. Break down `mul_eq_zero.mp hprod with h0 | h0` into its components or cases. Establish `hx : ξ = algebraMap F E r` using `sub_eq_zero.mp h0`.

Rewrite using `[← hσξ, hx, hfix]`. Establish `hx : ξ = -algebraMap F E r` using `eq_neg_of_add_eq_zero_left h0`. Rewrite using `[← hσξ, hx, map_neg, hfix]`. Establish `: 2 * ξ = 0` using `by linear_combination hcontra`. Conclude with `hξ0 ((mul_eq_zero.mp this).resolve_left h2E)`.
-/
theorem cm_exists_sqrt_nonsquare : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∃ d : F, (∀ r : F, r ^ 2 ≠ d) ∧ ∃ ξ : E, ξ ^ 2 = algebraMap F E d ∧ σ ξ = -ξ := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨-, hC, h2, hconj⟩ := h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)

  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  set τ : E →+* ℂ := w.embedding with hτ

  have hne : ∃ e : E, σ e ≠ e := by
    by_contra hall
    push_neg at hall
    have hreal : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      have := hconj τ x
      rw [hall x] at this
      simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hC.isComplex w))
      (InfinitePlace.isReal_iff.mpr hreal)

  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hconj, hconj, star_star]
  obtain ⟨e, he⟩ := hne
  set ξ : E := e - σ e with hξ
  have hξ0 : ξ ≠ 0 := fun h0 => he (sub_eq_zero.mp h0).symm
  have hσξ : σ ξ = -ξ := by
    simp only [hξ, map_sub, hinv, neg_sub]
  have h2E : (2 : E) ≠ 0 := two_ne_zero

  have hli : LinearIndependent F ![(1 : E), ξ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hst' : algebraMap F E s + algebraMap F E t * ξ = 0 := by
      simpa [Algebra.smul_def] using hst
    have hσ' : algebraMap F E s - algebraMap F E t * ξ = 0 := by
      have := congrArg σ hst'
      simpa [map_add, map_mul, AlgHom.commutes, hσξ, sub_eq_add_neg] using this
    have hs : algebraMap F E s = 0 := by
      have : 2 * algebraMap F E s = 0 := by linear_combination hst' + hσ'
      exact (mul_eq_zero.mp this).resolve_left h2E
    have ht : algebraMap F E t * ξ = 0 := by
      have : 2 * (algebraMap F E t * ξ) = 0 := by linear_combination hst' - hσ'
      exact (mul_eq_zero.mp this).resolve_left h2E
    refine ⟨(map_eq_zero _).mp hs, (map_eq_zero _).mp ((mul_eq_zero.mp ht).resolve_right hξ0)⟩
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
  have hmem : ξ ^ 2 ∈ Submodule.span F (Set.range ![(1 : E), ξ]) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hmem
  rw [Fin.sum_univ_two] at hc
  have hc' : algebraMap F E (c 0) + algebraMap F E (c 1) * ξ = ξ ^ 2 := by
    simpa [Algebra.smul_def] using hc
  have hc'' : algebraMap F E (c 0) - algebraMap F E (c 1) * ξ = ξ ^ 2 := by
    have := congrArg σ hc'
    simpa [map_add, map_mul, map_pow, AlgHom.commutes, hσξ, sub_eq_add_neg] using this
  have hb : algebraMap F E (c 1) * ξ = 0 := by
    have : 2 * (algebraMap F E (c 1) * ξ) = 0 := by linear_combination hc' - hc''
    exact (mul_eq_zero.mp this).resolve_left h2E
  have hsq : ξ ^ 2 = algebraMap F E (c 0) := by
    rw [← hc', hb, add_zero]
  refine ⟨c 0, ?_, ξ, hsq, hσξ⟩
  intro r hr
  have hfix : ∀ x : F, σ (algebraMap F E x) = algebraMap F E x := σ.commutes
  have hprod : (ξ - algebraMap F E r) * (ξ + algebraMap F E r) = 0 := by
    have : algebraMap F E (c 0) = algebraMap F E r ^ 2 := by rw [← hr, map_pow]
    linear_combination hsq + this
  have hcontra : ξ = -ξ := by
    rcases mul_eq_zero.mp hprod with h0 | h0
    · have hx : ξ = algebraMap F E r := sub_eq_zero.mp h0
      rw [← hσξ, hx, hfix]
    · have hx : ξ = -algebraMap F E r := eq_neg_of_add_eq_zero_left h0
      rw [← hσξ, hx, map_neg, hfix]
  have : 2 * ξ = 0 := by linear_combination hcontra
  exact hξ0 ((mul_eq_zero.mp this).resolve_left h2E)

end GlobalTheory.CompanionTheory.PlaneSA
