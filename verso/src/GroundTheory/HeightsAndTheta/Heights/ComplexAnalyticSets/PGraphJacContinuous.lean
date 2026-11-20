import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGraphJacContinuous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open scoped InnerProductSpace

/- English proof (translation)
Use `set S : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) := 1 + LinearMap.adjoint B ∘ₗ B with hSdef`. Establish `hBB : (LinearMap.adjoint B ∘ₗ B).IsPositive` using `LinearMap.isPositive_adjoint_comp_self B`. Establish `hS : S.IsPositive` using `LinearMap.isPositive_one.add hBB`. Establish `hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k` using `finrank_euclideanSpace_fin`. Rewrite using `[hS.isSymmetric.det_eq_prod_eigenvalues hn]`.

Use `Finset.prod_pos fun i _ => ?_` and prove the remaining obligations. Use `set v := hS.isSymmetric.eigenvectorBasis hn i`. Establish `hv : ‖v‖ = 1` using `(hS.isSymmetric.eigenvectorBasis hn).orthonormal.1 i`. Establish `h1 : ⟪S v, v⟫_ℝ = hS.isSymmetric.eigenvalues hn i`. Rewrite using `[hS.isSymmetric.apply_eigenvectorBasis hn i]`.

Simplify using `[real_inner_smul_left, hv, v]`. Establish `h2 : ⟪S v, v⟫_ℝ = ‖v‖ ^ 2 + ⟪(LinearMap.adjoint B ∘ₗ B) v, v⟫_ℝ`. Rewrite using `[hSdef, LinearMap.add_apply, inner_add_left, Module.End.one_apply, real_inner_self_eq_norm_sq]`. Establish `h3 : 0 ≤ ⟪(LinearMap.adjoint B ∘ₗ B) v, v⟫_ℝ`. Simplify using `using hBB.re_inner_nonneg_left v`.

Establish `: 0 < (hS.isSymmetric.eigenvalues hn i : ℝ)`. Rewrite using `[← h1, h2, hv]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `using this`.
-/
theorem det_one_add_adjoint_comp_self_pos {k m : ℕ}
    (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < LinearMap.det ((1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
      LinearMap.adjoint B ∘ₗ B) := by
  set S : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) := 1 + LinearMap.adjoint B ∘ₗ B
    with hSdef
  have hBB : (LinearMap.adjoint B ∘ₗ B).IsPositive := LinearMap.isPositive_adjoint_comp_self B
  have hS : S.IsPositive := LinearMap.isPositive_one.add hBB
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  rw [hS.isSymmetric.det_eq_prod_eigenvalues hn]
  refine Finset.prod_pos fun i _ => ?_
  set v := hS.isSymmetric.eigenvectorBasis hn i
  have hv : ‖v‖ = 1 := (hS.isSymmetric.eigenvectorBasis hn).orthonormal.1 i
  have h1 : ⟪S v, v⟫_ℝ = hS.isSymmetric.eigenvalues hn i := by
    rw [hS.isSymmetric.apply_eigenvectorBasis hn i]
    simp [real_inner_smul_left, hv, v]
  have h2 : ⟪S v, v⟫_ℝ = ‖v‖ ^ 2 + ⟪(LinearMap.adjoint B ∘ₗ B) v, v⟫_ℝ := by
    rw [hSdef, LinearMap.add_apply, inner_add_left, Module.End.one_apply, real_inner_self_eq_norm_sq]
  have h3 : 0 ≤ ⟪(LinearMap.adjoint B ∘ₗ B) v, v⟫_ℝ := by
    simpa using hBB.re_inner_nonneg_left v
  have : 0 < (hS.isSymmetric.eigenvalues hn i : ℝ) := by
    rw [← h1, h2, hv]; linarith
  simpa using this

/- English proof (translation)
The claim follows from `Real.sqrt_pos.mpr (det_one_add_adjoint_comp_self_pos B)`.
-/
theorem graphJac_pos {k m : ℕ} (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < graphJac B :=
  Real.sqrt_pos.mpr (det_one_add_adjoint_comp_self_pos B)

/- English proof (translation)
Establish `hc : Continuous fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) => (1 + (ContinuousLinearMap.adjoint B).comp B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))` using `continuous_const.add ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)`. Establish `heq : (fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) => graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) = fun B => √((1 + (ContinuousLinearMap.adjoint B).comp B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)).det)`. Use function extensionality and compare the values at `B`. Both sides reduce to the same expression. Rewrite using `[heq]`.

Conclude with `(ContinuousLinearMap.continuous_det.comp hc).sqrt`.
-/
theorem continuous_graphJac (k m : ℕ) :
    Continuous fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  have hc : Continuous fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      (1 + (ContinuousLinearMap.adjoint B).comp B :
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :=
    continuous_const.add ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)
  have heq : (fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) =
      fun B => √((1 + (ContinuousLinearMap.adjoint B).comp B :
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)).det) := by
    funext B
    rfl
  rw [heq]
  exact (ContinuousLinearMap.continuous_det.comp hc).sqrt

/- English proof (translation)
Introduce `k m A ε hε`. Use `set g := fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) => graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) with hg`. Establish `hgA : 0 < g A` using `graphJac_pos _`. Use `set η := ε * g A / (1 + ε) with hη`. Establish `hη0 : 0 < η` using `by positivity`.

Establish `hηe : (1 + ε) * η = ε * g A` using `by rw [hη]; field_simp`. Take `⟨δ, hδ, hδη⟩` from `Metric.continuous_iff.mp (continuous_graphJac k m) A η hη0`. Use `⟨δ / 2, half_pos hδ, fun B hB => ?_⟩` and prove the remaining obligations. Establish `hd : dist B A < δ` using `by rw [dist_eq_norm]; linarith`. Establish `h` using `hδη B hd`.

Rewrite `h` using `[Real.dist_eq, abs_lt]`. Express the relevant statement in the definitionally equal form `g B ≤ (1 + ε) * g A ∧ g A ≤ (1 + ε) * g B`. Prove the components needed by the constructor for the conclusion. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem GraphJacContinuous.proof : GraphJacContinuous.Statement := by
  intro k m A ε hε
  set g := fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
    graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) with hg
  have hgA : 0 < g A := graphJac_pos _
  set η := ε * g A / (1 + ε) with hη
  have hη0 : 0 < η := by positivity
  have hηe : (1 + ε) * η = ε * g A := by rw [hη]; field_simp
  obtain ⟨δ, hδ, hδη⟩ := Metric.continuous_iff.mp (continuous_graphJac k m) A η hη0
  refine ⟨δ / 2, half_pos hδ, fun B hB => ?_⟩
  have hd : dist B A < δ := by rw [dist_eq_norm]; linarith
  have h := hδη B hd
  rw [Real.dist_eq, abs_lt] at h
  change g B ≤ (1 + ε) * g A ∧ g A ≤ (1 + ε) * g B
  constructor
  · nlinarith
  · nlinarith

end

end GroundTheory.Heights₂.Heights
