import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LogpdAnalytic
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open ReciprocityTheory.AnForm ReciprocityTheory.L2DbarEstimates Filter Topology

/- English proof (translation)
Establish `hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h (c + L y)`. Establish `h1 : ∀ᶠ z in 𝓝 (c + L x), DifferentiableAt ℝ h z` using `(hh.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)`. Establish `hg : ContinuousAt (fun y => c + L y) x` using `(continuous_const.add L.continuous).continuousAt`. Conclude with `hg.eventually h1`. Establish `heq : fderiv ℝ (fun y => h (c + L y)) =ᶠ[𝓝 x] fun y => (fderiv ℝ h (c + L y)).comp L` using `by filter_upwards [hd] with y hy`.

Establish `hgd : HasFDerivAt (fun y => c + L y) L y` using `(L.hasFDerivAt).const_add c`. Conclude with `(hy.hasFDerivAt.comp y hgd).fderiv`. Rewrite using `[heq.fderiv_eq]`. Establish `hd2 : DifferentiableAt ℝ (fderiv ℝ h) (c + L x)` using `(hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero`. Establish `hF : HasFDerivAt (fun y => fderiv ℝ h (c + L y)) ((fderiv ℝ (fderiv ℝ h) (c + L x)).comp L) x` using `hd2.hasFDerivAt.comp x ((L.hasFDerivAt).const_add c)`.

Establish `hG : HasFDerivAt (fun y => (fderiv ℝ h (c + L y)).comp L) (((ContinuousLinearMap.compL ℝ E F ℝ).flip L).comp ((fderiv ℝ (fderiv ℝ h) (c + L x)).comp L)) x` using `((ContinuousLinearMap.compL ℝ E F ℝ).flip L).hasFDerivAt.comp x hF`. Rewrite using `[hG.fderiv]`. Both sides reduce to the same expression.
-/
theorem snd_affine {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (h : F → ℝ) (c : F) (L : E →L[ℝ] F) (x : E) (hh : ContDiffAt ℝ 2 h (c + L x))
    (w : E) :
    fderiv ℝ (fderiv ℝ (fun y => h (c + L y))) x w w = fderiv ℝ (fderiv ℝ h) (c + L x) (L w) (L w) := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h (c + L y) := by
    have h1 : ∀ᶠ z in 𝓝 (c + L x), DifferentiableAt ℝ h z :=
      (hh.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have hg : ContinuousAt (fun y => c + L y) x := (continuous_const.add L.continuous).continuousAt
    exact hg.eventually h1
  have heq : fderiv ℝ (fun y => h (c + L y)) =ᶠ[𝓝 x] fun y => (fderiv ℝ h (c + L y)).comp L := by
    filter_upwards [hd] with y hy
    have hgd : HasFDerivAt (fun y => c + L y) L y := (L.hasFDerivAt).const_add c
    exact (hy.hasFDerivAt.comp y hgd).fderiv
  rw [heq.fderiv_eq]
  have hd2 : DifferentiableAt ℝ (fderiv ℝ h) (c + L x) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hF : HasFDerivAt (fun y => fderiv ℝ h (c + L y)) ((fderiv ℝ (fderiv ℝ h) (c + L x)).comp L) x :=
    hd2.hasFDerivAt.comp x ((L.hasFDerivAt).const_add c)
  have hG : HasFDerivAt (fun y => (fderiv ℝ h (c + L y)).comp L)
      (((ContinuousLinearMap.compL ℝ E F ℝ).flip L).comp ((fderiv ℝ (fderiv ℝ h) (c + L x)).comp L)) x :=
    ((ContinuousLinearMap.compL ℝ E F ℝ).flip L).hasFDerivAt.comp x hF
  rw [hG.fderiv]
  rfl

def lineL {n : ℕ} (u : V n) : (Fin 1 → ℂ) →L[ℝ] V n :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight u).restrictScalars ℝ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lineL_apply {n : ℕ} (u : V n) (v : Fin 1 → ℂ) : lineL u v = v 0 • u := rfl

/- English proof (translation)
Establish `h : ∀ k, ((ξ k).re • bas n k + (ξ k).im • (Complex.I • bas n k)) = ξ k • bas n k` using `fun k => by`. Rewrite using `[← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]`. Use `congr 1`. Conclude with `Complex.re_add_im (ξ k)`. Establish `hsum : ∑ k, ξ k • bas n k = WithLp.toLp 2 ξ`.

Use extensionality with `j`. Simplify using `[bas, EuclideanSpace.single_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']`. Repeatedly rewrite using `[h]`. Conclude with `hsum`.
-/
theorem sum_bas_re {n : ℕ} (ξ : Fin n → ℂ) :
    (∑ k, ((ξ k).re • bas n k + (ξ k).im • (Complex.I • bas n k))) = WithLp.toLp 2 ξ := by
  have h : ∀ k, ((ξ k).re • bas n k + (ξ k).im • (Complex.I • bas n k)) = ξ k • bas n k := fun k => by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]
    congr 1
    exact Complex.re_add_im (ξ k)
  have hsum : ∑ k, ξ k • bas n k = WithLp.toLp 2 ξ := by
    ext j
    simp [bas, EuclideanSpace.single_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp_rw [h]
  exact hsum

/- English proof (translation)
Establish `h : ∀ k, ((ξ k).re • (Complex.I • bas n k) - (ξ k).im • bas n k) = Complex.I • (ξ k • bas n k)` using `fun k => by`. Rewrite using `[← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul, ← sub_smul]`. Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp`. Establish `hsum : ∑ k, ξ k • bas n k = WithLp.toLp 2 ξ`.

Use extensionality with `j`. Simplify using `[bas, EuclideanSpace.single_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']`. Repeatedly rewrite using `[h, ← Finset.smul_sum, hsum]`.
-/
theorem sum_bas_im {n : ℕ} (ξ : Fin n → ℂ) :
    (∑ k, ((ξ k).re • (Complex.I • bas n k) - (ξ k).im • bas n k)) = Complex.I • WithLp.toLp 2 ξ := by
  have h : ∀ k, ((ξ k).re • (Complex.I • bas n k) - (ξ k).im • bas n k) = Complex.I • (ξ k • bas n k) :=
      fun k => by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul, ← sub_smul]
    congr 1
    apply Complex.ext <;> simp
  have hsum : ∑ k, ξ k • bas n k = WithLp.toLp 2 ξ := by
    ext j
    simp [bas, EuclideanSpace.single_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp_rw [h, ← Finset.smul_sum, hsum]

/- English proof (translation)
Establish `e` using `Y.LocalMaximumSecondDerivative.leviV_re_eq hh ξ`. Rewrite `e` using `[sum_bas_re, sum_bas_im]`. Establish `L0 : z + lineL (WithLp.toLp 2 ξ) 0 = z` using `by simp [lineL_apply]`. Establish `L1 : lineL (WithLp.toLp 2 ξ) (fun _ => 1) = WithLp.toLp 2 ξ` using `by simp [lineL_apply]`. Establish `L2 : lineL (WithLp.toLp 2 ξ) (Complex.I • fun _ => 1) = Complex.I • WithLp.toLp 2 ξ`.

Simplify using `[lineL_apply]`. Establish `h0 : ContDiffAt ℝ 2 h (z + lineL (WithLp.toLp 2 ξ) 0)` using `by rw [L0]; exact hh`. Establish `s1` using `snd_affine h z (lineL (WithLp.toLp 2 ξ)) 0 h0 (fun _ => 1)`. Establish `s2` using `snd_affine h z (lineL (WithLp.toLp 2 ξ)) 0 h0 (Complex.I • fun _ => 1)`. Rewrite `s1` using `[L0, L1]`.

Rewrite `s2` using `[L0, L2]`. Unfold `levi`. Rewrite using `[s1, s2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem leviV_re_line {n : ℕ} (h : V n → ℝ) (z : V n) (hh : ContDiffAt ℝ 2 h z) (ξ : Fin n → ℂ) :
    (leviV n (fun y => (h y : ℂ)) z ξ).re =
      levi (fun v : Fin 1 → ℂ => h (z + lineL (WithLp.toLp 2 ξ) v)) 0 (fun _ => 1) := by
  have e := Y.LocalMaximumSecondDerivative.leviV_re_eq hh ξ
  rw [sum_bas_re, sum_bas_im] at e
  have L0 : z + lineL (WithLp.toLp 2 ξ) 0 = z := by simp [lineL_apply]
  have L1 : lineL (WithLp.toLp 2 ξ) (fun _ => 1) = WithLp.toLp 2 ξ := by simp [lineL_apply]
  have L2 : lineL (WithLp.toLp 2 ξ) (Complex.I • fun _ => 1) = Complex.I • WithLp.toLp 2 ξ := by
    simp [lineL_apply]
  have h0 : ContDiffAt ℝ 2 h (z + lineL (WithLp.toLp 2 ξ) 0) := by rw [L0]; exact hh
  have s1 := snd_affine h z (lineL (WithLp.toLp 2 ξ)) 0 h0 (fun _ => 1)
  have s2 := snd_affine h z (lineL (WithLp.toLp 2 ξ)) 0 h0 (Complex.I • fun _ => 1)
  rw [L0, L1] at s1
  rw [L0, L2] at s2
  unfold levi
  rw [s1, s2]
  linarith

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
