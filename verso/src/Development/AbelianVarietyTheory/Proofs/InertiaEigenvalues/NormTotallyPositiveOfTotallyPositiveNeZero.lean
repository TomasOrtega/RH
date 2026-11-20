import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Use `letI : Algebra E ℂ := (Complex.ofRealHom.comp φ).toAlgebra`. Establish `hmap : ∀ x, algebraMap E ℂ x = ((φ x : ℝ) : ℂ)` using `fun x => rfl`. Establish `key` using `Algebra.norm_eq_prod_embeddings E ℂ a`. Set `g : (E' →ₐ[E] ℂ) → (E' →ₐ[E] ℂ)` to `fun σ => { (starRingEnd ℂ).comp σ.toRingHom with commutes' := fun x => by show (starRingEnd ℂ) (σ (algebraMap E E' x)) = algebraMap E ℂ x`. Rewrite using `[σ.commutes, hmap, Complex.conj_ofReal] }`.

Establish `hg : ∀ σ x, g σ x = (starRingEnd ℂ) (σ x)` using `fun σ x => rfl`. Establish `hne : ∀ σ : E' →ₐ[E] ℂ, σ a ≠ 0` using `fun σ => (map_ne_zero σ).2 ha`. Establish `hnorm : ∀ σ : E' →ₐ[E] ℂ, ((‖σ a‖ : ℝ) : ℂ) ≠ 0` using `fun σ => by`. Conclude with `(norm_ne_zero_iff.2 (hne σ))` after adjusting the coercions. Establish `h1 : ∏ σ : E' →ₐ[E] ℂ, σ a / ((‖σ a‖ : ℝ) : ℂ) = 1`.

Use `Finset.prod_involution (fun σ _ => g σ) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_` and prove the remaining obligations. Introduce `σ _`. Rewrite using `[hg, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, div_eq_one_iff_eq (mul_ne_zero (hnorm σ) (hnorm σ)), Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Introduce `σ _ hf hgs`. Apply `hf` to reduce the goal to its premises. Establish `hreal : ComplexEmbedding.IsReal σ.toRingHom`. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`.

Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `congrArg (fun τ : E' →ₐ[E] ℂ => τ x) hgs`. Establish `hc : σ a = ((hreal.embedding a : ℝ) : ℂ)` using `(hreal.coe_embedding_apply a).symm`. Establish `hp` using `hpos hreal.embedding`. Rewrite using `[hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]`.

Conclude with `div_self (by exact_mod_cast hp.ne')`. Introduce `σ _`. Use extensionality with `x`. Simplify using `[hg]`. Rewrite `h1` using `[Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun σ _ => hnorm σ)]`.

Rewrite `key` using `[h1, hmap]`. Establish `hr : φ (Algebra.norm E a) = ∏ σ : E' →ₐ[E] ℂ, ‖σ a‖`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[key]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[hr]`. Conclude with `Finset.prod_pos fun σ _ => norm_pos_iff.2 (hne σ)`.
-/
theorem norm_pos_of_totallyPositive (E E' : Type) [Field E] [NumberField E] [Field E']
    [NumberField E'] [Algebra E E'] (a : E') (ha : a ≠ 0) (hpos : ∀ φ : E' →+* ℝ, 0 < φ a)
    (φ : E →+* ℝ) : 0 < φ (Algebra.norm E a) := by
  letI : Algebra E ℂ := (Complex.ofRealHom.comp φ).toAlgebra
  have hmap : ∀ x, algebraMap E ℂ x = ((φ x : ℝ) : ℂ) := fun x => rfl
  have key := Algebra.norm_eq_prod_embeddings E ℂ a
  let g : (E' →ₐ[E] ℂ) → (E' →ₐ[E] ℂ) := fun σ =>
    { (starRingEnd ℂ).comp σ.toRingHom with
      commutes' := fun x => by
        show (starRingEnd ℂ) (σ (algebraMap E E' x)) = algebraMap E ℂ x
        rw [σ.commutes, hmap, Complex.conj_ofReal] }
  have hg : ∀ σ x, g σ x = (starRingEnd ℂ) (σ x) := fun σ x => rfl
  have hne : ∀ σ : E' →ₐ[E] ℂ, σ a ≠ 0 := fun σ => (map_ne_zero σ).2 ha
  have hnorm : ∀ σ : E' →ₐ[E] ℂ, ((‖σ a‖ : ℝ) : ℂ) ≠ 0 := fun σ => by
    exact_mod_cast (norm_ne_zero_iff.2 (hne σ))
  have h1 : ∏ σ : E' →ₐ[E] ℂ, σ a / ((‖σ a‖ : ℝ) : ℂ) = 1 := by
    refine Finset.prod_involution (fun σ _ => g σ) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
    · intro σ _
      rw [hg, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, div_eq_one_iff_eq
        (mul_ne_zero (hnorm σ) (hnorm σ)), Complex.normSq_eq_norm_sq]
      push_cast; ring
    · intro σ _ hf hgs
      apply hf
      have hreal : ComplexEmbedding.IsReal σ.toRingHom := by
        rw [ComplexEmbedding.isReal_iff]
        ext x
        rw [ComplexEmbedding.conjugate_coe_eq]
        exact congrArg (fun τ : E' →ₐ[E] ℂ => τ x) hgs
      have hc : σ a = ((hreal.embedding a : ℝ) : ℂ) := (hreal.coe_embedding_apply a).symm
      have hp := hpos hreal.embedding
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
      exact div_self (by exact_mod_cast hp.ne')
    · intro σ _
      ext x
      simp [hg]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun σ _ => hnorm σ)]
    at h1
  rw [h1, hmap] at key
  have hr : φ (Algebra.norm E a) = ∏ σ : E' →ₐ[E] ℂ, ‖σ a‖ := by
    apply Complex.ofReal_injective
    rw [key]; push_cast; rfl
  rw [hr]
  exact Finset.prod_pos fun σ _ => norm_pos_iff.2 (hne σ)

end GlobalTheory
