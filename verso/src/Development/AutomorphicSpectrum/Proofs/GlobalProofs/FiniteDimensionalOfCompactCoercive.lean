import Mathlib

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.Glob

/- English proof (translation)
Introduce `H _ _ _ A hA S c hc hS`. Establish `hS' : ∀ u ∈ S.topologicalClosure, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re`. Introduce `u hu`. Establish `hcl : IsClosed {u : H | c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re}` using `isClosed_le (continuous_const.mul (continuous_norm.pow 2)) (Complex.continuous_re.comp (continuous_id.inner A.continuous))`. Establish `hsub : (S : Set H) ⊆ {u : H | c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re}` using `fun u hu ↦ hS u hu`.

Establish `h` using `closure_minimal hsub hcl`. Rewrite `h` using `[← Submodule.topologicalClosure_coe]`. Conclude with `h hu`. Establish `hbd : ∀ u ∈ S.topologicalClosure, ‖u‖ ≤ c⁻¹ * ‖A u‖`. Introduce `u hu`.

Establish `h1` using `hS' u hu`. Establish `h2 : (⟪u, A u⟫_ℂ).re ≤ ‖u‖ * ‖A u‖` using `(Complex.re_le_norm _).trans (norm_inner_le_norm _ _)`. Establish `h3 : c * ‖u‖ ≤ ‖A u‖`. Break down `(norm_nonneg u).eq_or_lt with h0 | hpos` into its components or cases. Rewrite using `[← h0, mul_zero]`.

Conclude with `norm_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[inv_mul_eq_div, le_div_iff₀ hc]`. Combine the linear equalities and inequalities to obtain the conclusion. Set `T : S.topologicalClosure →L[ℂ] H` to `A.comp S.topologicalClosure.subtypeL`.

Establish `hT : IsCompactOperator T` using `hA.comp_clm S.topologicalClosure.subtypeL`. Establish `hanti : AntilipschitzWith (Real.toNNReal c⁻¹) T`. Use `ContinuousLinearMap.antilipschitz_of_bound T fun x ↦ ?_` and prove the remaining obligations. Rewrite using `[Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]`. Conclude with `hbd x x.2`.

Establish `hemb : Topology.IsClosedEmbedding T` using `hanti.isClosedEmbedding T.uniformContinuous`. Establish `hK` using `IsCompactOperator.isCompact_closure_image_closedBall (f := (T : S.topologicalClosure →ₗ[ℂ] H)) hT 1`. Establish `hball : IsCompact (Metric.closedBall (0 : S.topologicalClosure) 1)`. Use `(hemb.isCompact_preimage hK).of_isClosed_subset Metric.isClosed_closedBall ?_` and prove the remaining obligations. Introduce `x hx`.

Conclude with `subset_closure ⟨x, hx, rfl⟩`. Establish `: FiniteDimensional ℂ S.topologicalClosure` using `FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one hball`. Conclude with `Submodule.finiteDimensional_of_le S.le_topologicalClosure`.
-/
theorem finiteDimensional_of_compact_coercive :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H),
      IsCompactOperator A → ∀ (S : Submodule ℂ H) (c : ℝ), 0 < c →
        (∀ u ∈ S, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) → FiniteDimensional ℂ S := by
  intro H _ _ _ A hA S c hc hS
  have hS' : ∀ u ∈ S.topologicalClosure, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re := by
    intro u hu
    have hcl : IsClosed {u : H | c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re} :=
      isClosed_le (continuous_const.mul (continuous_norm.pow 2))
        (Complex.continuous_re.comp (continuous_id.inner A.continuous))
    have hsub : (S : Set H) ⊆ {u : H | c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re} := fun u hu ↦ hS u hu
    have h := closure_minimal hsub hcl
    rw [← Submodule.topologicalClosure_coe] at h
    exact h hu
  have hbd : ∀ u ∈ S.topologicalClosure, ‖u‖ ≤ c⁻¹ * ‖A u‖ := by
    intro u hu
    have h1 := hS' u hu
    have h2 : (⟪u, A u⟫_ℂ).re ≤ ‖u‖ * ‖A u‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    have h3 : c * ‖u‖ ≤ ‖A u‖ := by
      rcases (norm_nonneg u).eq_or_lt with h0 | hpos
      · rw [← h0, mul_zero]
        exact norm_nonneg _
      · nlinarith
    rw [inv_mul_eq_div, le_div_iff₀ hc]
    linarith
  let T : S.topologicalClosure →L[ℂ] H := A.comp S.topologicalClosure.subtypeL
  have hT : IsCompactOperator T := hA.comp_clm S.topologicalClosure.subtypeL
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) T := by
    refine ContinuousLinearMap.antilipschitz_of_bound T fun x ↦ ?_
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]
    exact hbd x x.2
  have hemb : Topology.IsClosedEmbedding T := hanti.isClosedEmbedding T.uniformContinuous
  have hK := IsCompactOperator.isCompact_closure_image_closedBall
    (f := (T : S.topologicalClosure →ₗ[ℂ] H)) hT 1
  have hball : IsCompact (Metric.closedBall (0 : S.topologicalClosure) 1) := by
    refine (hemb.isCompact_preimage hK).of_isClosed_subset Metric.isClosed_closedBall ?_
    intro x hx
    exact subset_closure ⟨x, hx, rfl⟩
  have : FiniteDimensional ℂ S.topologicalClosure :=
    FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one hball
  exact Submodule.finiteDimensional_of_le S.le_topologicalClosure

end GlobalTheory.CompanionTheory.Glob
