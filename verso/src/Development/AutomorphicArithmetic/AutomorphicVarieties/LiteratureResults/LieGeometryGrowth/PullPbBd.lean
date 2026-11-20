import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullCorrBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldFlow
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

/- English proof (translation)
Introduce `E _ _ _ a ho U Ξ Y C hY W hW q`. Take `⟨B₁, hB₁, hc⟩` from `corrBd E a U Ξ C q`. Take `⟨B₂, hB₂, hf⟩` from `fieldBd E a U Y C hY W hW`. Take `⟨hfl, hflow⟩` from `fieldFlow E a ho U Ξ Y C hY W hW`. Use `⟨B₁ * (2 * B₂) ^ q, by positivity, fun α α' w hα hw hw' g M hM hb X => ?_⟩` and prove the remaining obligations.

Take `⟨y, x, hyx⟩ : ∃ (y : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)), (retractOne g : KernelIndexFullLattice.G1 E a).1 = infGL E a y * finGL E a x` from `⟨_, _, (GlobalTheory.CuspRep.infGL_mul_finGL _).symm⟩`. Establish `hYg : Y (infGL E a y * finGL E a x) = Y g`. Take `⟨t, ht⟩` from `(retrFacts E a).1 g`. Rewrite using `[← hyx, ht, ← hY.left 1 t g, map_one, one_mul]`. Take `⟨h, hh, h1, h2⟩` from `hY.root g 1 (by simp)`.

Establish `hbd` using `hb h (by rw [hh, one_smul])`. Establish `hpt` using `hflow y h x 1 (by rw [hYg]; exact hh)`. Use `choose v' hv' hv'' using hf y x 1 (by simp)`. Establish `hmem : sand y (hOne E a) ∈ (geo ho U Ξ).Y` using `sand_mem_cone y hOne_mem_cone`. Establish `e1` using `hw' y x X`.

Rewrite `e1` using `[(omApply _ _ _ _ (geo ho U Ξ) W hfl q).1 w _ _ hmem, pb_apply, hpt]`. Establish `e2 : (fun i => fderiv ℝ (flow (W (x : GL (Fin a) (Af E) ⧸ U)) 1) (sand y (hOne E a)) ((2 : ℝ) • sand y (hv (X i)))) = fun i => sand y (v' ((2 : ℝ) • hv (X i)))`. Use function extensionality and compare the values at `i`. Rewrite using `[← hv'', map_smul (sand y)]`. Rewrite `e1` using `[e2]`.

Establish `e3` using `hc α w.1 hα hw g y h x M hyx h1 h2 hM hbd (fun i => v' ((2 : ℝ) • hv (X i)))`. Establish `e4 : Ξ.mat y⁻¹ * Ξ.mat y = 1`. Rewrite using `[← map_mul, inv_mul_cancel, map_one]`. Rewrite `e3` using `[e1, Matrix.mulVec_mulVec, e4, Matrix.one_mulVec, ← hyx]`. Use `e3.trans ?_` and prove the remaining obligations.

Establish `e5 : ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ (2 * B₂) ^ q * ∏ i, ‖hv (X i)‖`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => (hv' _).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[norm_smul, Real.norm_ofNat]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Lit.Geo.pbBd :
    PbBd := by
  intro E _ _ _ a ho U Ξ Y C hY W hW q
  obtain ⟨B₁, hB₁, hc⟩ := corrBd E a U Ξ C q
  obtain ⟨B₂, hB₂, hf⟩ := fieldBd E a U Y C hY W hW
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hY W hW
  refine ⟨B₁ * (2 * B₂) ^ q, by positivity, fun α α' w hα hw hw' g M hM hb X => ?_⟩
  obtain ⟨y, x, hyx⟩ : ∃ (y : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
      (retractOne g : KernelIndexFullLattice.G1 E a).1 = infGL E a y * finGL E a x :=
    ⟨_, _, (GlobalTheory.CuspRep.infGL_mul_finGL _).symm⟩
  have hYg : Y (infGL E a y * finGL E a x) = Y g := by
    obtain ⟨t, ht⟩ := (retrFacts E a).1 g
    rw [← hyx, ht, ← hY.left 1 t g, map_one, one_mul]
  obtain ⟨h, hh, h1, h2⟩ := hY.root g 1 (by simp)
  have hbd := hb h (by rw [hh, one_smul])
  have hpt := hflow y h x 1 (by rw [hYg]; exact hh)
  choose v' hv' hv'' using hf y x 1 (by simp)
  have hmem : sand y (hOne E a) ∈ (geo ho U Ξ).Y := sand_mem_cone y hOne_mem_cone
  have e1 := hw' y x X
  rw [(omApply _ _ _ _ (geo ho U Ξ) W hfl q).1 w _ _ hmem, pb_apply, hpt] at e1
  have e2 : (fun i => fderiv ℝ (flow (W (x : GL (Fin a) (Af E) ⧸ U)) 1) (sand y (hOne E a))
      ((2 : ℝ) • sand y (hv (X i)))) = fun i => sand y (v' ((2 : ℝ) • hv (X i))) := by
    funext i
    rw [← hv'', map_smul (sand y)]
  rw [e2] at e1
  have e3 := hc α w.1 hα hw g y h x M hyx h1 h2 hM hbd (fun i => v' ((2 : ℝ) • hv (X i)))
  have e4 : Ξ.mat y⁻¹ * Ξ.mat y = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [e1, Matrix.mulVec_mulVec, e4, Matrix.one_mulVec, ← hyx] at e3
  refine e3.trans ?_
  have e5 : ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ (2 * B₂) ^ q * ∏ i, ‖hv (X i)‖ := by
    calc ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ ∏ i, (2 * B₂) * ‖hv (X i)‖ := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => (hv' _).trans (le_of_eq ?_)
          rw [norm_smul, Real.norm_ofNat]
          ring
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc B₁ * M * ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ B₁ * M * ((2 * B₂) ^ q * ∏ i, ‖hv (X i)‖) :=
        mul_le_mul_of_nonneg_left e5 (mul_nonneg hB₁ hM)
    _ = _ := by ring
