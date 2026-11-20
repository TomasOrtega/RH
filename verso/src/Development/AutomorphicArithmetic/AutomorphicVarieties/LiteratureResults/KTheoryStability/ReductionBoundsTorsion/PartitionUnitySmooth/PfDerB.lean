import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.QuadBd

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL PositivityTheory.KB PositivityTheory.KB.SmoothPartitionUnityBasic.DerivationBounds Filter Topology

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

/- English proof (translation)
Rewrite using `[mat_actL, star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]`.
-/
private theorem d_rel {L : Type} [Field L] [NumberField L] {N : ℕ} (g : Gp L N) (h : HS L N)
    (z : VR L N) (w : InfinitePlace L) :
    star (z w) ⬝ᵥ (mat (actL g h) w *ᵥ z w) =
      star ((((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *ᵥ z w) ⬝ᵥ
        (mat h w *ᵥ ((((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *ᵥ z w)) := by
  rw [mat_actL, star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]

/- English proof (translation)
The claim follows from `|qR (actL x v) z| ≤ N * ‖v‖ * qR (actL x (one L N).1) z := by unfold qR rw [Finset.mul_sum] refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_) rw [d_rel, d_rel] have h1 : mat (one L N).1 w = 1 := rfl rw [h1, one_mulVec] refine quad_bd N (mat v w) ‖v‖ ( …`.
-/
private theorem d_key {L : Type} [Field L] [NumberField L] {N : ℕ} (x : Gp L N) (v : HS L N) (z : VR L N) :
    |qR (actL x v) z| ≤ N * ‖v‖ * qR (actL x (one L N).1) z := by
  unfold qR
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [d_rel, d_rel]
  have h1 : mat (one L N).1 w = 1 := rfl
  rw [h1, one_mulVec]
  refine quad_bd N (mat v w) ‖v‖ (norm_nonneg _) (fun a b => ?_) _
  exact ((norm_le_pi_norm (v.1 w a) b).trans (norm_le_pi_norm (v.1 w) a)).trans
    ((norm_le_pi_norm v.1 w).trans le_rfl)

/- English proof (translation)
Introduce `L _ _ N φ x B ε hB hε hd hl`. Use `set p := actL x (one L N).1 with hp`. Use `ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.comp_apply]`. Use `set u := actL x v with hu`.

Establish `hline : HasDerivAt (fun t : ℝ => φ (p + t • u)) ((fderiv ℝ φ p) u) 0`. Establish `h1 : HasDerivAt (fun t : ℝ => p + t • u) u 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p`. Establish `hD : HasFDerivAt φ (fderiv ℝ φ p) (p + (0 : ℝ) • u)`. Simplify using `using hd.hasFDerivAt`.

Conclude with `hD.comp_hasDerivAt (0 : ℝ) h1`. Establish `hlim` using `hline.tendsto_slope_zero_right.norm`. Use `set K : ℝ := N * ‖v‖ with hK`. Establish `hK0 : 0 ≤ K` using `by positivity`. Use `le_of_tendsto hlim ?_` and prove the remaining obligations.

Establish `hmem : Set.Ioo (0 : ℝ) (ε / (K + 1)) ∈ 𝓝[>] (0 : ℝ)` using `Ioo_mem_nhdsGT (by positivity)`. Use `filter_upwards [hmem] with t ht`. Take `⟨ht0, ht1⟩` from `ht`. Establish `hδε : K * t ≤ ε`. Establish `: (K + 1) * t < ε` using `by rwa [lt_div_iff₀ (by positivity), mul_comm] at ht1`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hcl : Cl (K * t) p (p + t • u)`. Introduce `z`. Establish `e : qR (p + t • u) z = qR p z + t * qR u z`. Rewrite using `[← evR_apply, map_add, map_smul, evR_apply, evR_apply, smul_eq_mul]`.

Rewrite using `[e, add_sub_cancel_left, abs_mul, abs_of_pos ht0]`. Use `d_key x v z` as an intermediate fact. Rewrite `this` using `[← hu, ← hp]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hb` using `hl (K * t) (by positivity) hδε _ hcl`.

Simplify using `only [zero_add, zero_smul, add_zero, smul_eq_mul, norm_mul, norm_inv, Real.norm_eq_abs, abs_of_pos ht0]`. Rewrite using `[inv_mul_le_iff₀ ht0]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pf_DerB : DerB := by
  intro L _ _ N φ x B ε hB hε hd hl
  set p := actL x (one L N).1 with hp
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [ContinuousLinearMap.comp_apply]
  set u := actL x v with hu
  have hline : HasDerivAt (fun t : ℝ => φ (p + t • u)) ((fderiv ℝ φ p) u) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => p + t • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p
    have hD : HasFDerivAt φ (fderiv ℝ φ p) (p + (0 : ℝ) • u) := by
      simpa using hd.hasFDerivAt
    exact hD.comp_hasDerivAt (0 : ℝ) h1
  have hlim := hline.tendsto_slope_zero_right.norm
  set K : ℝ := N * ‖v‖ with hK
  have hK0 : 0 ≤ K := by positivity
  refine le_of_tendsto hlim ?_
  have hmem : Set.Ioo (0 : ℝ) (ε / (K + 1)) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hmem] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hδε : K * t ≤ ε := by
    have : (K + 1) * t < ε := by rwa [lt_div_iff₀ (by positivity), mul_comm] at ht1
    nlinarith
  have hcl : Cl (K * t) p (p + t • u) := by
    intro z
    have e : qR (p + t • u) z = qR p z + t * qR u z := by
      rw [← evR_apply, map_add, map_smul, evR_apply, evR_apply, smul_eq_mul]
    rw [e, add_sub_cancel_left, abs_mul, abs_of_pos ht0]
    have := d_key x v z
    rw [← hu, ← hp] at this
    nlinarith
  have hb := hl (K * t) (by positivity) hδε _ hcl
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul, norm_mul, norm_inv, Real.norm_eq_abs,
    abs_of_pos ht0]
  rw [inv_mul_le_iff₀ ht0]
  nlinarith

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
