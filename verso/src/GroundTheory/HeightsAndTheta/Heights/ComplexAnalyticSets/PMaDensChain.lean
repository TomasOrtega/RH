import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsPiola
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMaDensChain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensLeibniz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

namespace MaDensChain

variable {D : ℕ}

/- English proof (translation)
The claim follows from `(hh.hasDerivAt.comp_hasFDerivAt y hg.hasFDerivAt).fderiv`.
-/
theorem fderiv_comp_real (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    fderiv ℝ (h ∘ g) y = deriv h (g y) • fderiv ℝ g y :=
  (hh.hasDerivAt.comp_hasFDerivAt y hg.hasFDerivAt).fderiv

/- English proof (translation)
Rewrite using `[dz_cplx, dz_cplx, fderiv_comp_real h g y hh hg]`. Simplify using `only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dz_cplx_comp (j : Fin D) (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    dz j (cplx (h ∘ g)) y = ((deriv h (g y) : ℝ) : ℂ) * dz j (cplx g) y := by
  rw [dz_cplx, dz_cplx, fderiv_comp_real h g y hh hg]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[dzb_cplx, dzb_cplx, fderiv_comp_real h g y hh hg]`. Simplify using `only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dzb_cplx_comp (k : Fin D) (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    dzb k (cplx (h ∘ g)) y = ((deriv h (g y) : ℝ) : ℂ) * dzb k (cplx g) y := by
  rw [dzb_cplx, dzb_cplx, fderiv_comp_real h g y hh hg]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/- English proof (translation)
Take `⟨U, hU, hzU, hgU, -⟩` from `MaDensLeibniz.exists_open_contDiffOn g g z hg hg`. Establish `hF1 : Differentiable ℝ F` using `hF.differentiable (by norm_num)`. Establish `hF' : Differentiable ℝ (deriv F)` using `(hF.deriv' (n := 1)).differentiable (by norm_num)`. Use extensionality with `j k`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`.

Rewrite using `[hessCDz_thm D _ U hU (hF.comp_contDiffOn hgU) z hzU j k, hessCDz_thm D g U hU hgU z hzU j k]`. Establish `hev : dzb k (cplx (F ∘ g)) =ᶠ[𝓝 z] fun y => cplx (deriv F ∘ g) y * dzb k (cplx g) y` using `by filter_upwards [hU.mem_nhds hzU] with y hy`. Conclude with `dzb_cplx_comp k F g y (hF1 _) ((hgU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))`. Establish `hgd : DifferentiableAt ℝ g z` using `hg.differentiableAt (by norm_num)`. Establish `hA : DifferentiableAt ℝ (cplx (deriv F ∘ g)) z`.

Establish `h : cplx (deriv F ∘ g) = fun y => Complex.ofRealCLM ((deriv F ∘ g) y)`. Use function extensionality and compare the values at `y`. Simplify using `[cplx]`. Rewrite using `[h]`. Conclude with `Complex.ofRealCLM.differentiableAt.comp z ((hF' _).comp z hgd)`.

Establish `hB` using `differentiableAt_dzb (j := k) (MaDensLeibniz.contDiffAt_cplx hg)`. Rewrite using `[dz_congr hev, dz_mul hA hB, dz_cplx_comp j (deriv F) g z (hF' _) hgd]`. Simplify using `only [gradMat, cplx, Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hessC_comp_real (F : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hF : ContDiff ℝ 2 F)
    (hg : ContDiffAt ℝ 2 g z) :
    hessC (F ∘ g) z = ((deriv F (g z) : ℝ) : ℂ) • hessC g z + ((deriv (deriv F) (g z) : ℝ) : ℂ) • gradMat g g z := by
  obtain ⟨U, hU, hzU, hgU, -⟩ := MaDensLeibniz.exists_open_contDiffOn g g z hg hg
  have hF1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hF' : Differentiable ℝ (deriv F) :=
    (hF.deriv' (n := 1)).differentiable (by norm_num)
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU (hF.comp_contDiffOn hgU) z hzU j k, hessCDz_thm D g U hU hgU z hzU j k]
  have hev : dzb k (cplx (F ∘ g)) =ᶠ[𝓝 z] fun y => cplx (deriv F ∘ g) y * dzb k (cplx g) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_comp k F g y (hF1 _)
      ((hgU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hgd : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (cplx (deriv F ∘ g)) z := by
    have h : cplx (deriv F ∘ g) = fun y => Complex.ofRealCLM ((deriv F ∘ g) y) := by
      funext y; simp [cplx]
    rw [h]
    exact Complex.ofRealCLM.differentiableAt.comp z ((hF' _).comp z hgd)
  have hB := differentiableAt_dzb (j := k) (MaDensLeibniz.contDiffAt_cplx hg)
  rw [dz_congr hev, dz_mul hA hB, dz_cplx_comp j (deriv F) g z (hF' _) hgd]
  simp only [gradMat, cplx, Function.comp_apply]
  ring

/- English proof (translation)
Use extensionality with `j k`. Simplify using `only [gradMat, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[dz_cplx_comp j F g z hF hg, dzb_cplx_comp k F g z hF hg]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gradMat_comp (F : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hF : DifferentiableAt ℝ F (g z)) (hg : DifferentiableAt ℝ g z) :
    gradMat (F ∘ g) (F ∘ g) z = ((deriv F (g z) ^ 2 : ℝ) : ℂ) • gradMat g g z := by
  ext j k
  simp only [gradMat, Matrix.smul_apply, smul_eq_mul]
  rw [dz_cplx_comp j F g z hF hg, dzb_cplx_comp k F g z hF hg]
  push_cast
  ring

/- English proof (translation)
Introduce `D φ F g z hF hg`. Establish `hF1 : DifferentiableAt ℝ F (g z)` using `(hF.differentiable (by norm_num)) _`. Prove the components needed by the constructor for the conclusion. Rewrite using `[maDens_cons_eq, maDens_cons_eq, hessC_comp_real F g z hF hg]`. Unfold `gradDens`.

Rewrite using `[mdisc_cons_smul_add]`. Simplify using `only [Complex.add_re, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree. Unfold `gradDens`. Rewrite using `[gradMat_comp F g z hF1 (hg.differentiableAt (by norm_num)), mdisc_cons_smul_fst]`.

Simplify using `only [Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem proof : MaDensChain.Statement := by
  intro D φ F g z hF hg
  have hF1 : DifferentiableAt ℝ F (g z) := (hF.differentiable (by norm_num)) _
  constructor
  · rw [maDens_cons_eq, maDens_cons_eq, hessC_comp_real F g z hF hg]
    unfold gradDens
    rw [mdisc_cons_smul_add]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  · unfold gradDens
    rw [gradMat_comp F g z hF1 (hg.differentiableAt (by norm_num)), mdisc_cons_smul_fst]
    simp only [Complex.re_ofReal_mul]
    ring

end MaDensChain

end

end GroundTheory.Heights₂.Heights
