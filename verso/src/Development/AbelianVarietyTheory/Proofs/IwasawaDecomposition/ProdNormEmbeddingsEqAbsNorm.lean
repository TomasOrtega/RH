import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

/- English proof (translation)
Establish `h` using `Algebra.norm_eq_prod_embeddings ℚ ℂ γ`. Establish `h2` using `congrArg (fun z : ℂ => ‖z‖) h`. Simplify using `only [norm_prod, eq_ratCast] at h2`. Rewrite using `[Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => ‖φ γ‖) (fun φ : E →ₐ[ℚ] ℂ => ‖φ γ‖) (fun _ => rfl), ← h2]`. Rewrite using `[← Real.norm_eq_abs, ← Complex.norm_real]`.

Simplify using the standard rewrite rules.
-/
theorem prod_norm_embeddings_eq_abs_norm (E : Type) [Field E] [NumberField E] (γ : E) :
    ∏ φ : E →+* ℂ, ‖φ γ‖ = |((Algebra.norm ℚ γ : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ γ
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_prod, eq_ratCast] at h2
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => ‖φ γ‖)
    (fun φ : E →ₐ[ℚ] ℂ => ‖φ γ‖) (fun _ => rfl), ← h2]
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  simp

/- English proof (translation)
Introduce `E _ _ _ _ r n hr K _ hK γ σ`. Set `s : (E →+* ℂ) → (E →+* ℂ)` to `fun τ => σ.comp (τ.codRestrict K (hK τ))`. Establish `hs : ∀ τ x, s τ x = σ ⟨τ x, hK τ x⟩` using `fun _ _ => rfl`. Establish `hinj : Function.Injective s`. Introduce `a b hab`.

Use extensionality with `x`. Use `DFunLike.congr_fun hab x` as an intermediate fact. Rewrite `this` using `[hs, hs]`. Conclude with `congrArg Subtype.val (σ.injective this)`. Establish `hbij : Function.Bijective s` using `Finite.injective_iff_bijective.mp hinj`.

Establish `hconj : ∀ τ, ‖s (ComplexEmbedding.conjugate τ) γ‖ = ‖s τ γ‖`. Introduce `τ`. Establish `h1 : s (ComplexEmbedding.conjugate τ) γ = s τ (IsCMField.complexConj E γ)`. Rewrite using `[hs, hs]`. Use `congr 2`.

Rewrite using `[IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]`. Rewrite using `[h1, IsCMField.complexEmbedding_complexConj, Complex.norm_conj]`. Establish `hinv : Function.Involutive (fun τ : E →+* ℂ => ComplexEmbedding.conjugate τ)` using `fun τ => star_star τ`. Establish `hP : ‖σ (∏ τ : E →+* ℂ, (⟨τ γ, hK τ γ⟩ : K) ^ r τ)‖ = ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r τ`. Rewrite using `[map_prod, norm_prod]`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, norm_pow, hs]`. Establish `hQ : ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r τ = ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r (ComplexEmbedding.conjugate τ)`. Rewrite using `[← hinv.bijective.prod_comp (fun τ => ‖s τ γ‖ ^ r τ)]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[hconj]`. Rewrite using `[hP, sq]`. Use `nth_rewrite 2 [hQ]`. Rewrite using `[← Finset.prod_mul_distrib, ← prod_norm_embeddings_eq_abs_norm, ← hbij.prod_comp (fun φ => ‖φ γ‖), ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[← pow_add, hr]`.
-/
theorem norm_typeNorm_sq_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ), (∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) → ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (γ : E) (σ : K →+* ℂ), ‖σ (∏ τ : E →+* ℂ, (⟨τ γ, hK τ γ⟩ : K) ^ r τ)‖ ^ 2 = |(Algebra.norm ℚ γ : ℝ)| ^ n := by
  intro E _ _ _ _ r n hr K _ hK γ σ
  let s : (E →+* ℂ) → (E →+* ℂ) := fun τ => σ.comp (τ.codRestrict K (hK τ))
  have hs : ∀ τ x, s τ x = σ ⟨τ x, hK τ x⟩ := fun _ _ => rfl
  have hinj : Function.Injective s := by
    intro a b hab
    ext x
    have := DFunLike.congr_fun hab x
    rw [hs, hs] at this
    exact congrArg Subtype.val (σ.injective this)
  have hbij : Function.Bijective s := Finite.injective_iff_bijective.mp hinj
  have hconj : ∀ τ, ‖s (ComplexEmbedding.conjugate τ) γ‖ = ‖s τ γ‖ := by
    intro τ
    have h1 : s (ComplexEmbedding.conjugate τ) γ = s τ (IsCMField.complexConj E γ) := by
      rw [hs, hs]
      congr 2
      rw [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
    rw [h1, IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
  have hinv : Function.Involutive
      (fun τ : E →+* ℂ => ComplexEmbedding.conjugate τ) := fun τ => star_star τ
  have hP : ‖σ (∏ τ : E →+* ℂ, (⟨τ γ, hK τ γ⟩ : K) ^ r τ)‖ = ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r τ := by
    rw [map_prod, norm_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, norm_pow, hs]
  have hQ : ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r τ
      = ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r (ComplexEmbedding.conjugate τ) := by
    rw [← hinv.bijective.prod_comp (fun τ => ‖s τ γ‖ ^ r τ)]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hconj]
  rw [hP, sq]
  nth_rewrite 2 [hQ]
  rw [← Finset.prod_mul_distrib, ← prod_norm_embeddings_eq_abs_norm,
    ← hbij.prod_comp (fun φ => ‖φ γ‖), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← pow_add, hr]

end GlobalTheory.Mem
