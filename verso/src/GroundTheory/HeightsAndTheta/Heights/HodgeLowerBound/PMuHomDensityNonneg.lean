import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuHomDensityNonneg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuSheetLeviNonneg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ComplexHessianTransposeIsHermitian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

/- English proof (translation)
Unfold `maDensity`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mixedDiscriminant_constant]`. Establish `hS : IsSymmSndFDerivAt ℝ φ y` using `hφ.isSymmSndFDerivAt (by simp)`. Establish `hP` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.complexHessian_posSemidef hS (zero_le_one' ℝ) hL`. Establish `hd` using `hP.det_nonneg`.

Rewrite `hd` using `[Complex.ofReal_one, one_smul, Matrix.det_transpose]`. Establish `hre : 0 ≤ (cxHessian φ y).det.re` using `(Complex.nonneg_iff.1 hd).1`. Establish `h1 : (0 : ℝ) ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D` using `by positivity`. Conclude with `mul_nonneg h1 hre`.
-/
theorem maDensity_const_nonneg {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (hφ : ContDiffAt ℝ 2 φ y)
    (hL : ∀ v, 0 ≤ leviForm φ y v) : 0 ≤ maDensity (fun _ : Fin D => φ) y := by
  unfold maDensity
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mixedDiscriminant_constant]
  have hS : IsSymmSndFDerivAt ℝ φ y := hφ.isSymmSndFDerivAt (by simp)
  have hP := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.complexHessian_posSemidef hS (zero_le_one' ℝ) hL
  have hd := hP.det_nonneg
  rw [Complex.ofReal_one, one_smul, Matrix.det_transpose] at hd
  have hre : 0 ≤ (cxHessian φ y).det.re := (Complex.nonneg_iff.1 hd).1
  have h1 : (0 : ℝ) ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D := by positivity
  exact mul_nonneg h1 hre

/- English proof (translation)
Introduce `II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X Q hQ`. Use `filter_upwards [h II Ψ K ι Ω E D O Lt X Q hQ] with y hy w`. Unfold `sheetDensity`. Use `split_ifs with hγ`. Take `⟨h2, hL⟩` from `hy w _ hγ.choose_spec`.

Rewrite using `[one_mul]`. Conclude with `maDensity_const_nonneg h2 hL`. Conclude with `le_rfl`.
-/
theorem MuHomDensityNonneg.proof (h : MuSheetLeviNonneg.Statement) : MuHomDensityNonneg.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X Q hQ
  filter_upwards [h II Ψ K ι Ω E D O Lt X Q hQ] with y hy w
  unfold sheetDensity
  split_ifs with hγ
  · obtain ⟨h2, hL⟩ := hy w _ hγ.choose_spec
    rw [one_mul]
    exact maDensity_const_nonneg h2 hL
  · exact le_rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
