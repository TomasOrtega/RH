import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullMatBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullCentreVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneReal
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

/- English proof (translation)
Introduce `E _ _ _ a U Ξ C q`. Take `⟨B, hB, hM⟩` from `matBd E a Ξ C`. Take `⟨r, hr⟩` from `oneReal E a Ξ`. Take `⟨T, hT⟩` from `(retrFacts E a).2.2 C`. Use `⟨B * Real.exp (|r| * T) * B ^ q, by positivity, ?_⟩` and prove the remaining obligations.

Introduce `α w hα hw g y h x M hg h1 h2 hM0 hbd v`. Take `⟨m1, -, m3⟩` from `hM h h1 h2`. Take `⟨t, ht, e⟩` from `hT g h h1 h2`. Apply the tactic sequence `have hcomm : infGL E a h * finGL E a x = finGL E a x * infGL E a h := by first | exact GlobalTheory.CuspRep.infGL_comm _ _ | exact TR.infGL_comm _ _`. Rewrite `e` using `[hg, mul_assoc, ← hcomm, ← mul_assoc, ← map_mul]`.

Use `set X : Fin q → Herm E a := fun i => hv.symm ((1 / 2 : ℝ) • sand h⁻¹ (v i)) with hX`. Establish `hc` using `hw (y * h) x X`. Establish `hv' : (fun i => (2 : ℝ) • sand (y * h) (hv (X i))) = fun i => sand y (v i)`. Use function extensionality and compare the values at `i`. Simplify using `only [hX, LinearEquiv.apply_symm_apply, map_smul, smul_smul]`.

Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_right]`. Evaluate the numerical expressions. Establish `hcv` using `centreVal E a U Ξ r hr q α hα X 1 t (GroundTheory.Automorphic.CuspidalSpectrum.retractOne (g * infGL E a h) : KernelIndexFullLattice.G1 E a).1`. Rewrite `hcv` using `[map_one, one_mul]`. Rewrite `hc` using `[hv', e, hcv]`.

Rewrite using `[hc, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel_left]`. Use `(m1 _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_smul]`. Establish `hexp : ‖Complex.exp (-(r * t))‖ ≤ Real.exp (|r| * T)`. Rewrite using `[Complex.norm_exp]`.

Use `Real.exp_le_exp.2 ?_` and prove the remaining obligations. Establish `: (-((r : ℂ) * t)).re = -(r * t)` using `by simp`. Rewrite using `[this]`. Use `(neg_le_abs _).trans ?_` and prove the remaining obligations. Rewrite using `[abs_mul]`.

Conclude with `mul_le_mul_of_nonneg_left ht (abs_nonneg _)`. Establish `hp : ∏ i, ‖hv (X i)‖ ≤ B ^ q * ∏ i, ‖v i‖`. Establish `: B ^ q * ∏ i, ‖v i‖ = ∏ i, B * ‖v i‖`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[this]`.

Use `Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_` and prove the remaining obligations. Simplify using `only [hX, LinearEquiv.apply_symm_apply]`. Rewrite using `[norm_smul]`. Establish `h3` using `m3 (v i)`. Establish `h4` using `norm_nonneg (sand h⁻¹ (v i))`.

Establish `h5 : ‖(1 / 2 : ℝ)‖ = 1 / 2` using `by norm_num`. Rewrite using `[h5]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb` using `(hbd X).trans (mul_le_mul_of_nonneg_left hp hM0)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Lit.Geo.corrBd :
    CorrBd := by
  intro E _ _ _ a U Ξ C q
  obtain ⟨B, hB, hM⟩ := matBd E a Ξ C
  obtain ⟨r, hr⟩ := oneReal E a Ξ
  obtain ⟨T, hT⟩ := (retrFacts E a).2.2 C
  refine ⟨B * Real.exp (|r| * T) * B ^ q, by positivity, ?_⟩
  intro α w hα hw g y h x M hg h1 h2 hM0 hbd v
  obtain ⟨m1, -, m3⟩ := hM h h1 h2
  obtain ⟨t, ht, e⟩ := hT g h h1 h2
  have hcomm : infGL E a h * finGL E a x = finGL E a x * infGL E a h := by
    first | exact GlobalTheory.CuspRep.infGL_comm _ _ | exact TR.infGL_comm _ _
  rw [hg, mul_assoc, ← hcomm, ← mul_assoc, ← map_mul] at e
  set X : Fin q → Herm E a := fun i => hv.symm ((1 / 2 : ℝ) • sand h⁻¹ (v i)) with hX
  have hc := hw (y * h) x X
  have hv' : (fun i => (2 : ℝ) • sand (y * h) (hv (X i))) = fun i => sand y (v i) := by
    funext i
    simp only [hX, LinearEquiv.apply_symm_apply, map_smul, smul_smul]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_right]
    norm_num
  have hcv := centreVal E a U Ξ r hr q α hα X 1 t
    (GroundTheory.Automorphic.CuspidalSpectrum.retractOne (g * infGL E a h) : KernelIndexFullLattice.G1 E a).1
  rw [map_one, one_mul] at hcv
  rw [hv', e, hcv] at hc
  rw [hc, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel_left]
  refine (m1 _).trans ?_
  rw [norm_smul]
  have hexp : ‖Complex.exp (-(r * t))‖ ≤ Real.exp (|r| * T) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have : (-((r : ℂ) * t)).re = -(r * t) := by simp
    rw [this]
    refine (neg_le_abs _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  have hp : ∏ i, ‖hv (X i)‖ ≤ B ^ q * ∏ i, ‖v i‖ := by
    have : B ^ q * ∏ i, ‖v i‖ = ∏ i, B * ‖v i‖ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [this]
    refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
    simp only [hX, LinearEquiv.apply_symm_apply]
    rw [norm_smul]
    have h3 := m3 (v i)
    have h4 := norm_nonneg (sand h⁻¹ (v i))
    have h5 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [h5]
    linarith
  have hb := (hbd X).trans (mul_le_mul_of_nonneg_left hp hM0)
  calc _ ≤ B * (Real.exp (|r| * T) * (M * (B ^ q * ∏ i, ‖v i‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hexp hb (norm_nonneg _) (Real.exp_pos _).le) hB
    _ = _ := by ring
