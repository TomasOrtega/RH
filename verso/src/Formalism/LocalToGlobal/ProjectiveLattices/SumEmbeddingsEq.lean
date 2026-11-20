import Mathlib

noncomputable section

namespace Formalism.L2.Pj.DatLin

open NumberField ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Rewrite using `[← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings ℂ]`. Conclude with `Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)`.
-/
theorem sum_embeddings_eq (z : E) :
    (((Algebra.trace ℚ E z : ℚ) : ℂ)) = ∑ σ : E →+* ℂ, σ z := by
  rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings ℂ]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)

/- English proof (translation)
Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[Complex.ofReal_ratCast, sum_embeddings_eq, ← Finset.sum_add_sum_compl Ψ]`. Establish `hc : ∑ σ ∈ Ψᶜ, σ z = ∑ τ ∈ Ψ, conj (τ z)`. Use `Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `σ hσ`.

Simplify using `only [Finset.mem_coe, Finset.mem_compl] at hσ ⊢`. Rewrite using `[hΨ, show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ from star_star σ]`. Conclude with `hσ`. Introduce `τ hτ`. Simplify using `only [Finset.mem_coe, Finset.mem_compl]`.

Conclude with `(hΨ τ).mp hτ`. Introduce `σ _`. Conclude with `star_star σ`. Introduce `τ _`. Conclude with `star_star τ`.

Introduce `σ _`. Simplify using `[ComplexEmbedding.conjugate_coe_eq]`. Rewrite using `[hc, ← Finset.sum_add_distrib, Complex.ofReal_sum]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[Complex.add_conj]`.
-/
theorem trace_eq_sum_psi (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ ∈ Ψ, 2 * (τ z).re := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, sum_embeddings_eq, ← Finset.sum_add_sum_compl Ψ]

  have hc : ∑ σ ∈ Ψᶜ, σ z = ∑ τ ∈ Ψ, conj (τ z) := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_coe, Finset.mem_compl] at hσ ⊢
      rw [hΨ, show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ from star_star σ]
      exact hσ
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_compl]
      exact (hΨ τ).mp hτ
    · intro σ _; exact star_star σ
    · intro τ _; exact star_star τ
    · intro σ _; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [hc, ← Finset.sum_add_distrib, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Complex.add_conj]

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem sesq_repr [StarRing E] {V : Type} [AddCommGroup V] [Module E V] {ι : Type} [Fintype ι]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (b : Module.Basis ι E V) (x y : V) :
    h x y = ∑ i, ∑ j, star (b.repr x i) * h (b i) (b j) * b.repr y j := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Formalism.L2.Pj.DatLin
