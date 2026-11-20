import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ApplySmooth

noncomputable section

open UpperTheory.V.Lit.Dr
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo

/- English proof (translation)
Introduce `V' V F _ _ _ _ _ _ _ _ q H w p hH hw`. Establish `hr : minSmoothness ℝ 2 ≤ ∞`. Rewrite using `[minSmoothness_of_isRCLikeNormedField]`. Conclude with `WithTop.coe_le_coe.2 le_top`. Establish `hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞`.

Conclude with `le_top` after adjusting the coercions. Use `⟨?_, extDeriv_pullback (hw.differentiableAt (by simp)) hH hr⟩` and prove the remaining obligations. Apply `altSmooth V' V' F q (pb H w) p` to reduce the goal to its premises. Introduce `v`. Establish `h1 : ContDiffAt ℝ ∞ (fun y => w (H y)) p` using `hw.comp p hH`.

Establish `h2 : ∀ i, ContDiffAt ℝ ∞ (fun y => fderiv ℝ H y (v i)) p` using `fun i => (hH.fderiv_right hinf).clm_apply contDiffAt_const`. Establish `h3` using `applySmooth V' V F q (fun y => w (H y)) (fun i y => fderiv ℝ H y (v i)) p h1 h2`. Simplify `h3` using `[pb, Function.comp_def]`.
-/
theorem pbD : PbD := by
  intro V' V F _ _ _ _ _ _ _ _ q H w p hH hw
  have hr : minSmoothness ℝ 2 ≤ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    exact_mod_cast le_top
  refine ⟨?_, extDeriv_pullback (hw.differentiableAt (by simp)) hH hr⟩
  apply altSmooth V' V' F q (pb H w) p
  intro v
  have h1 : ContDiffAt ℝ ∞ (fun y => w (H y)) p := hw.comp p hH
  have h2 : ∀ i, ContDiffAt ℝ ∞ (fun y => fderiv ℝ H y (v i)) p := fun i =>
    (hH.fderiv_right hinf).clm_apply contDiffAt_const
  have h3 := applySmooth V' V F q (fun y => w (H y)) (fun i y => fderiv ℝ H y (v i)) p h1 h2
  simpa [pb, Function.comp_def] using h3

end UpperTheory.V.Lit.Geo
