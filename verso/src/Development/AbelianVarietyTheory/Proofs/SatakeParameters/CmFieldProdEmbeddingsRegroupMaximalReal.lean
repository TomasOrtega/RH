import Mathlib

open NumberField

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : InfinitePlace.mk τ = InfinitePlace.mk τ'`. Apply `(IsCMField.equivInfinitePlace E).injective` to reduce the goal to its premises. Rewrite using `[IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply, InfinitePlace.comap_mk, InfinitePlace.comap_mk, h]`. Break down `InfinitePlace.mk_eq_iff.1 h1 with h2 | h2` into its components or cases. Conclude with `Or.inl h2.symm`.

Conclude with `Or.inr h2.symm`.
-/
theorem cm_eq_or_conj_of_comp_eq (E : Type) [Field E] [NumberField E] [IsCMField E]
    (τ τ' : E →+* ℂ)
    (h : τ'.comp (algebraMap (maximalRealSubfield E) E) =
      τ.comp (algebraMap (maximalRealSubfield E) E)) :
    τ' = τ ∨ τ' = ComplexEmbedding.conjugate τ := by
  have h1 : InfinitePlace.mk τ = InfinitePlace.mk τ' := by
    apply (IsCMField.equivInfinitePlace E).injective
    rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply,
      InfinitePlace.comap_mk, InfinitePlace.comap_mk, h]
  rcases InfinitePlace.mk_eq_iff.1 h1 with h2 | h2
  · exact Or.inl h2.symm
  · exact Or.inr h2.symm

/- English proof (translation)
Establish `h` using `IsTotallyReal.complexEmbedding_isReal (τ.comp (algebraMap (maximalRealSubfield E) E))`. Rewrite `h` using `[ComplexEmbedding.isReal_iff]`. Conclude with `h`.
-/
theorem cm_conj_comp_eq (E : Type) [Field E] [NumberField E] (τ : E →+* ℂ) :
    (ComplexEmbedding.conjugate τ).comp (algebraMap (maximalRealSubfield E) E) =
      τ.comp (algebraMap (maximalRealSubfield E) E) := by
  have h := IsTotallyReal.complexEmbedding_isReal (τ.comp (algebraMap (maximalRealSubfield E) E))
  rw [ComplexEmbedding.isReal_iff] at h
  exact h

/- English proof (translation)
Use `⟨fun φ => k (ComplexEmbedding.lift E φ), fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_fiberwise Finset.univ (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E))]`. Use `Finset.prod_congr rfl fun φ _ => ?_` and prove the remaining obligations. Use `set τ₀ := ComplexEmbedding.lift E φ with hτ₀`. Establish `h0 : τ₀.comp (algebraMap (maximalRealSubfield E) E) = φ` using `ComplexEmbedding.lift_comp_algebraMap E φ`.

Establish `h1 : (ComplexEmbedding.conjugate τ₀).comp (algebraMap (maximalRealSubfield E) E) = φ`. Rewrite using `[cm_conj_comp_eq, h0]`. Establish `hne : τ₀ ≠ ComplexEmbedding.conjugate τ₀` using `fun h => IsTotallyComplex.complexEmbedding_not_isReal τ₀ (ComplexEmbedding.isReal_iff.2 h.symm)`. Establish `hfib : Finset.univ.filter (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E) = φ) = {τ₀, ComplexEmbedding.conjugate τ₀}`. Use extensionality with `τ`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `cm_eq_or_conj_of_comp_eq E τ₀ τ (h.trans h0.symm)`. Introduce and unpack `(rfl | rfl)`.

Conclude with `h0`. Conclude with `h1`. Rewrite using `[hfib, Finset.prod_pair hne, h0, h1, hk, mul_comm (2 : ℤ), zpow_mul, zpow_two]`.
-/
theorem cm_prod_regroup_maximalReal (E : Type) [Field E] [NumberField E] [IsCMField E]
    (k : (E →+* ℂ) → ℤ) (hk : ∀ τ, k (ComplexEmbedding.conjugate τ) = k τ) :
    ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, ∀ g : (maximalRealSubfield E →+* ℂ) → ℂ,
      ∏ τ : E →+* ℂ, g (τ.comp (algebraMap (maximalRealSubfield E) E)) ^ k τ =
        ∏ φ, g φ ^ (2 * n φ) := by
  classical
  refine ⟨fun φ => k (ComplexEmbedding.lift E φ), fun g => ?_⟩
  rw [← Finset.prod_fiberwise Finset.univ
    (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E))]
  refine Finset.prod_congr rfl fun φ _ => ?_
  set τ₀ := ComplexEmbedding.lift E φ with hτ₀
  have h0 : τ₀.comp (algebraMap (maximalRealSubfield E) E) = φ :=
    ComplexEmbedding.lift_comp_algebraMap E φ
  have h1 : (ComplexEmbedding.conjugate τ₀).comp (algebraMap (maximalRealSubfield E) E) = φ := by
    rw [cm_conj_comp_eq, h0]
  have hne : τ₀ ≠ ComplexEmbedding.conjugate τ₀ := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ₀ (ComplexEmbedding.isReal_iff.2 h.symm)
  have hfib : Finset.univ.filter
      (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E) = φ) =
      {τ₀, ComplexEmbedding.conjugate τ₀} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      exact cm_eq_or_conj_of_comp_eq E τ₀ τ (h.trans h0.symm)
    · rintro (rfl | rfl)
      · exact h0
      · exact h1
  rw [hfib, Finset.prod_pair hne, h0, h1, hk, mul_comm (2 : ℤ), zpow_mul, zpow_two]

end GlobalTheory
