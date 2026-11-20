import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos

/- English proof (translation)
Unfold `ReciprocityTheory.AnForm.M.IsPsh`. Introduce `x j y hy w`. Establish `hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x` using `⟨hy.1, hy.2.2⟩`. Establish `hfun : ((Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ).φ x ∘ (A.chart j).symm) = fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z`. Use function extensionality and compare the values at `z`.

Use `show Θ.φ x _ + 0 + Θ.φ x _ = (2 : ℝ) • Θ.φ x _`. Rewrite using `[smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlevi : ∀ z v, ReciprocityTheory.AnForm.levi (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) z v = 2 * ReciprocityTheory.AnForm.levi (Θ.φ x ∘ (A.chart j).symm) z v`. Introduce `z v`.

Unfold `ReciprocityTheory.AnForm.levi`. Establish `h1 : fderiv ℝ (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) = (2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)` using `fderiv_const_smul_of_field (2 : ℝ)`. Establish `h2 : fderiv ℝ ((2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)) = (2 : ℝ) • fderiv ℝ (fderiv ℝ (Θ.φ x ∘ (A.chart j).symm))` using `fderiv_const_smul_of_field (2 : ℝ)`. Rewrite using `[h1, h2]`. Simplify using `only [Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun, hlevi]`. Distinguish the cases in `hw : w = 0`. Substitute `hw` using the available equality. Simplify using `[ReciprocityTheory.AnForm.levi]`.

Conclude with `mul_nonneg (by norm_num) (hpos x j y hy' w hw).le`.
-/
theorem isPsh_add_zero_add (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ) :
    IsPsh A (Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ) := by
  unfold ReciprocityTheory.AnForm.M.IsPsh
  intro x j y hy w
  have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x := ⟨hy.1, hy.2.2⟩
  have hfun : ((Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ).φ x ∘ (A.chart j).symm) =
      fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show Θ.φ x _ + 0 + Θ.φ x _ = (2 : ℝ) • Θ.φ x _
    rw [smul_eq_mul]
    ring
  have hlevi : ∀ z v, ReciprocityTheory.AnForm.levi (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) z v =
      2 * ReciprocityTheory.AnForm.levi (Θ.φ x ∘ (A.chart j).symm) z v := by
    intro z v
    unfold ReciprocityTheory.AnForm.levi
    have h1 : fderiv ℝ (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) =
        (2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm) := fderiv_const_smul_of_field (2 : ℝ)
    have h2 : fderiv ℝ ((2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)) =
        (2 : ℝ) • fderiv ℝ (fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)) := fderiv_const_smul_of_field (2 : ℝ)
    rw [h1, h2]
    simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hfun, hlevi]
  by_cases hw : w = 0
  · subst hw
    simp [ReciprocityTheory.AnForm.levi]
  · exact mul_nonneg (by norm_num) (hpos x j y hy' w hw).le

end GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos
