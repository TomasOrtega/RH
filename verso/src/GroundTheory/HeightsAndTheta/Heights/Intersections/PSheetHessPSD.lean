import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StSheetHessPSD
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemiPosTwist
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterOsgood
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ComplexOrder

/- English proof (translation)
Take `⟨U, hU, hUo, hyU⟩` from `eventually_nhds_iff.mp h`. Rewrite using `[analyticAt_pi_iff]`. Introduce `p`. Conclude with `osgood e U (fun y' => γ y' p) hUo (fun y' hy' => ((differentiableAt_pi.mp (hU y' hy')) p).differentiableWithinAt) y hyU`.
-/
theorem analyticAt_of_eventually_differentiableAt {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {e : ℕ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (h : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') : AnalyticAt ℂ γ y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp h
  rw [analyticAt_pi_iff]
  intro p
  exact osgood e U (fun y' => γ y' p) hUo
    (fun y' hy' => ((differentiableAt_pi.mp (hU y' hy')) p).differentiableWithinAt) y hyU

/- English proof (translation)
Introduce `K _ ι _ P e Ψ M y w γ hM hPos hγ`. Establish `hev` using `hγ.2`. Establish `hγy : γ y ∈ mcPts P` using `hev.self_of_nhds.2.1`. Establish `hz : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0` using `hγy.1`. Establish `han : AnalyticAt ℂ γ y` using `analyticAt_of_eventually_differentiableAt (hev.mono fun _ h => h.1)`.

Establish `hUo` using `SemipositiveTwist.isOpen_noZeroBlock (ι := ι)`. Establish `hlog : ContDiffAt ℝ 2 (fun z => Real.log (M.h z)) (γ y)` using `((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos _ hz).ne'`. Establish `hcomp : (fun y' => Real.log (M.h (γ y'))) = (fun z => Real.log (M.h z)) ∘ γ` using `rfl`. Establish `hC2 : ContDiffAt ℝ 2 (fun y' => Real.log (M.h (γ y'))) y`. Rewrite using `[hcomp]`.

Conclude with `hlog.comp y (han.restrictScalars.contDiffAt)`. Use `show (ReciprocityTheory.AnForm.hessC (fun y' => Real.log (M.h (γ y'))) y).PosSemidef`. Use `ReciprocityTheory.AnForm.M.hessC_posSemidef _ y hC2 fun x => ?_` and prove the remaining obligations. Rewrite using `[hcomp, ReciprocityTheory.AnForm.levi_comp x han hlog]`. Establish `hL` using `SemipositiveTwist.laplacian_line_eq_levi hlog (fderiv ℂ γ y x)`.

Establish `hΔ` using `hPos (γ y) hz (fderiv ℂ γ y x)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem SheetHessPSD.proof : SheetHessPSD.Statement := by
  intro K _ ι _ P e Ψ M y w γ hM hPos hγ
  have hev := hγ.2
  have hγy : γ y ∈ mcPts P := hev.self_of_nhds.2.1
  have hz : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := hγy.1
  have han : AnalyticAt ℂ γ y :=
    analyticAt_of_eventually_differentiableAt (hev.mono fun _ h => h.1)
  have hUo := SemipositiveTwist.isOpen_noZeroBlock (ι := ι)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (M.h z)) (γ y) :=
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos _ hz).ne'
  have hcomp : (fun y' => Real.log (M.h (γ y'))) = (fun z => Real.log (M.h z)) ∘ γ := rfl
  have hC2 : ContDiffAt ℝ 2 (fun y' => Real.log (M.h (γ y'))) y := by
    rw [hcomp]
    exact hlog.comp y (han.restrictScalars.contDiffAt)
  show (ReciprocityTheory.AnForm.hessC (fun y' => Real.log (M.h (γ y'))) y).PosSemidef
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ y hC2 fun x => ?_
  rw [hcomp, ReciprocityTheory.AnForm.levi_comp x han hlog]
  have hL := SemipositiveTwist.laplacian_line_eq_levi hlog (fderiv ℂ γ y x)
  have hΔ := hPos (γ y) hz (fderiv ℂ γ y x)
  linarith

end GroundTheory.Heights₂.Heights.Inter
