import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

/- English proof (translation)
Introduce `r X z`. Establish `hall : ((Algebra.norm ℚ z : ℚ) : ℂ) = ∏ σ : E →+* ℂ, σ z`. Rewrite using `[← eq_ratCast (algebraMap ℚ ℂ), Algebra.norm_eq_prod_embeddings ℚ ℂ z]`. Conclude with `Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun _ => rfl)`. Establish `hcompl : ∏ σ ∈ X.Ψᶜ, σ z = ∏ τ ∈ X.Ψ, (starRingEnd ℂ) (τ z)`.

Use `Finset.prod_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `σ hσ`. Establish `h` using `X.cmType (ComplexEmbedding.conjugate σ)`. Rewrite `h` using `[ComplexEmbedding.involutive_conjugate E σ]`. Conclude with `h.mpr (Finset.mem_compl.mp hσ)`.

Introduce `τ hτ`. Conclude with `Finset.mem_compl.mpr ((X.cmType τ).mp hτ)`. Introduce `σ _`. Conclude with `ComplexEmbedding.involutive_conjugate E σ`. Introduce `τ _`.

Conclude with `ComplexEmbedding.involutive_conjugate E τ`. Introduce `σ _`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]`. Establish `hC : ((Algebra.norm ℚ z : ℚ) : ℂ) = ((∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[hall, ← Finset.prod_mul_prod_compl X.Ψ, hcompl, ← Finset.prod_mul_distrib, Finset.prod_coe_sort X.Ψ (fun τ => ‖τ z‖ ^ 2), Complex.ofReal_prod]`.

Use `Finset.prod_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[RCLike.mul_conj]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hR : ((Algebra.norm ℚ z : ℚ) : ℝ) = ∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[Complex.ofReal_ratCast]`. Conclude with `hC`. Establish `hnn : (0 : ℚ) ≤ Algebra.norm ℚ z`. Establish `h0 : (0 : ℝ) ≤ ((Algebra.norm ℚ z : ℚ) : ℝ)`.

Rewrite using `[hR]`. Check the signs of the components of the expression. Conclude with `h0` after adjusting the coercions. Rewrite using `[abs_of_nonneg hnn, hR]`.
-/
theorem abs_norm_eq_prod_cmType_sq :
    (∀ (r : ℕ) (X : Data E r) (z : E), ((|Algebra.norm ℚ z| : ℚ) : ℝ) = ∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2) := by
  classical
  intro r X z

  have hall : ((Algebra.norm ℚ z : ℚ) : ℂ) = ∏ σ : E →+* ℂ, σ z := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), Algebra.norm_eq_prod_embeddings ℚ ℂ z]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun _ => rfl)

  have hcompl : ∏ σ ∈ X.Ψᶜ, σ z = ∏ τ ∈ X.Ψ, (starRingEnd ℂ) (τ z) := by
    refine Finset.prod_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      have h := X.cmType (ComplexEmbedding.conjugate σ)
      rw [ComplexEmbedding.involutive_conjugate E σ] at h
      exact h.mpr (Finset.mem_compl.mp hσ)
    · intro τ hτ
      exact Finset.mem_compl.mpr ((X.cmType τ).mp hτ)
    · intro σ _
      exact ComplexEmbedding.involutive_conjugate E σ
    · intro τ _
      exact ComplexEmbedding.involutive_conjugate E τ
    · intro σ _
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  have hC : ((Algebra.norm ℚ z : ℚ) : ℂ) = ((∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2 : ℝ) : ℂ) := by
    rw [hall, ← Finset.prod_mul_prod_compl X.Ψ, hcompl, ← Finset.prod_mul_distrib,
      Finset.prod_coe_sort X.Ψ (fun τ => ‖τ z‖ ^ 2), Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    rw [RCLike.mul_conj]
    push_cast
    rfl
  have hR : ((Algebra.norm ℚ z : ℚ) : ℝ) = ∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_ratCast]
    exact hC
  have hnn : (0 : ℚ) ≤ Algebra.norm ℚ z := by
    have h0 : (0 : ℝ) ≤ ((Algebra.norm ℚ z : ℚ) : ℝ) := by
      rw [hR]
      positivity
    exact_mod_cast h0
  rw [abs_of_nonneg hnn, hR]

end GlobalTheory
