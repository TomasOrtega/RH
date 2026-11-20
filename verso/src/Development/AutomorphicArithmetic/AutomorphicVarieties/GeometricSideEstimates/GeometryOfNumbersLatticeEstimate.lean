import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.ScalingInvarianceOfGeometricFunctional
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GlobalGeometricEstimateOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.RationalPointRetractionExistsCmDatum
open UpperTheory.V.Lit.Geo NumberField

/- English proof (translation)
Introduce `E _ _ _ a ha L hL`. Use `letI : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin a × InfinitePlace E)) := InnerProductSpace.rclikeToReal ℂ _`. Use `⟨Module.finrank ℝ (EuclideanSpace ℂ (Fin a × InfinitePlace E)), fun g => ?_⟩` and prove the remaining obligations. Take `⟨C, N, hC, hmin⟩` from `UpperTheory.global_geometric_estimate_of_local E a ha L hL`. Take `⟨-, hrt, -⟩` from `UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha`.

Take `⟨B, hB⟩ : ∃ B : ℝ, ∀ v ∈ lat L (rt g), v ≠ 0 → 1 ≤ B * qf (pt (rt g) v)` from `⟨_, hmin (rt g)⟩`. Establish `hlat : lat L (rt g) = lat L g`. Unfold `lat`. Rewrite using `[(hrt g).2.2]`. Rewrite `hB` using `[hlat]`.

Set `φ : lat L g →+ EuclideanSpace ℂ (Fin a × InfinitePlace E)` to `(euc.toLinearMap.toAddMonoidHom.comp (pt (rt g))).comp (lat L g).subtype`. Establish `hφ : ∀ v : lat L g, ‖φ v‖ ^ 2 = qf (pt (rt g) v.1)` using `fun v => norm_euc_sq _`. Establish `hM : (0 : ℝ) < max B 1` using `lt_max_of_lt_right one_pos`. Establish `key` using `UpperTheory.scaling_invariance_of_geometric_functional (lat L g) (EuclideanSpace ℂ (Fin a × InfinitePlace E)) φ (Real.sqrt (1 / max B 1)) (Real.sqrt_pos.2 (by positivity)) (fun v hv => by`. Establish `h1` using `hB v.1 v.2 (fun h => hv (Subtype.ext h))`.

Rewrite `h1` using `[← hφ]`. Apply `Real.sqrt_le_iff.2` to reduce the goal to its premises. Use `⟨norm_nonneg _, ?_⟩` and prove the remaining obligations. Rewrite using `[div_le_iff₀ hM, mul_comm]`. Conclude with `h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))`.

Simplify `key` using `only [hφ]`.
-/
theorem UpperTheory.geometry_of_numbers_lattice_estimate :
    LatScale := by
  intro E _ _ _ a ha L hL
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin a × InfinitePlace E)) :=
    InnerProductSpace.rclikeToReal ℂ _
  refine ⟨Module.finrank ℝ (EuclideanSpace ℂ (Fin a × InfinitePlace E)), fun g => ?_⟩
  obtain ⟨C, N, hC, hmin⟩ := UpperTheory.global_geometric_estimate_of_local E a ha L hL
  obtain ⟨-, hrt, -⟩ := UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ v ∈ lat L (rt g), v ≠ 0 → 1 ≤ B * qf (pt (rt g) v) := ⟨_, hmin (rt g)⟩
  have hlat : lat L (rt g) = lat L g := by
    unfold lat
    rw [(hrt g).2.2]
  rw [hlat] at hB
  let φ : lat L g →+ EuclideanSpace ℂ (Fin a × InfinitePlace E) :=
    (euc.toLinearMap.toAddMonoidHom.comp (pt (rt g))).comp (lat L g).subtype
  have hφ : ∀ v : lat L g, ‖φ v‖ ^ 2 = qf (pt (rt g) v.1) := fun v => norm_euc_sq _
  have hM : (0 : ℝ) < max B 1 := lt_max_of_lt_right one_pos
  have key := UpperTheory.scaling_invariance_of_geometric_functional (lat L g) (EuclideanSpace ℂ (Fin a × InfinitePlace E)) φ
    (Real.sqrt (1 / max B 1)) (Real.sqrt_pos.2 (by positivity)) (fun v hv => by
      have h1 := hB v.1 v.2 (fun h => hv (Subtype.ext h))
      rw [← hφ] at h1
      apply Real.sqrt_le_iff.2
      refine ⟨norm_nonneg _, ?_⟩
      rw [div_le_iff₀ hM, mul_comm]
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
  simpa only [hφ] using key
