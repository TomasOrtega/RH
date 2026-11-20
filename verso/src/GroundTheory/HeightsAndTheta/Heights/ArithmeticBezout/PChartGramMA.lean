import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartGram
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChartGramPolar
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChartGramSchur
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChartGramHess
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open scoped InnerProductSpace
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (maDensity cxHessian)

/- English proof (translation)
Introduce `e n v y hv h0`. Take `⟨t, ht, hto, hyt⟩` from `eventually_nhds_iff.1 hv`. Establish `han : AnalyticOnNhd ℂ v t`. Establish `hd : DifferentiableOn ℂ v t` using `fun y' hy' => (ht y' hy').differentiableWithinAt`. Conclude with `AnalyticOnNhd.pi fun j => ReciprocityTheory.AnForm.Osgood.osgood e t _ hto (differentiableOn_pi.mp hd j)`.

Use `set L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm with hL`. Use `set u : (Fin e → ℂ) → EuclideanSpace ℂ (Fin n) := fun y' => L (v y') with hu_def`. Establish `hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y'` using `by filter_upwards [hto.mem_nhds hyt] with y' hy'`. Conclude with `(L : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).analyticAt _ |>.comp (han y' hy')`. Establish `hu0 : u y ≠ 0`.

Simplify `h0` using `[hu_def, hL, PiLp.coe_symm_continuousLinearEquiv]`. Establish `hDu : ∀ b, fderiv ℂ u y b = L (fderiv ℂ v y b)` using `fun b => by`. Establish `hc` using `(L : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).hasFDerivAt.comp y (hv.self_of_nhds).hasFDerivAt`. Establish `hc' : HasFDerivAt u _ y` using `hc`. Rewrite using `[hc'.fderiv]`.

Both sides reduce to the same expression. Establish `hφ : (fun (_ : Fin e) (y' : Fin e → ℂ) => Real.log ‖WithLp.toLp 2 (v y')‖) = fun _ y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re`. Use function extensionality and compare the values at `_ y'`. Establish `h` using `inner_self_eq_norm_sq (𝕜 := ℂ) (u y')`. Establish `h' : (⟪u y', u y'⟫_ℂ).re = ‖u y'‖ ^ 2` using `h`.

Rewrite using `[h', Real.log_pow]`. Simplify using `[hu_def, hL]`. Use `set w : Fin (e + 1) → EuclideanSpace ℂ (Fin n) := Fin.cons (u y) fun j => fderiv ℂ u y (Pi.single j 1) with hw`. Use `set G : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := Matrix.of fun a b => ⟪w a, w b⟫_ℂ with hG_def`. Establish `hmat : G = Matrix.of fun a b => ∑ i, star ((Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) a i) * (Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) b i`.

Use extensionality with `a b`. Apply the tactic sequence `refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>`. Apply the tactic sequence `simp only [hG_def, hw, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, hDu] <;>`. Apply the tactic sequence `simp only [PiLp.inner_apply, RCLike.inner_apply'] <;>`. Simplify using `[hu_def, hL]`.

Establish `hgram : gramVol v y = G.det.re`. Rewrite using `[hmat]`. Both sides reduce to the same expression. Establish `hG00 : G 0 0 ≠ 0`. Simplify `hu0` using `[hG_def, hw]`.

Establish `hcx : cxHessian (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y = (2 * G 0 0)⁻¹ • Matrix.transpose (Matrix.of fun i j : Fin e => G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0)`. Use extensionality with `i j`. Rewrite using `[ChartGram.cxHessian_half_log hu hu0]`. Simplify using `only [hG_def, hw, Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, smul_eq_mul]`. Establish `: ⟪u y, u y⟫_ℂ ≠ 0` using `by simpa [hG_def, hw] using hG00`.

Clear the denominators using the available nonvanishing facts. Establish `hS` using `ChartGram.det_eq_corner_mul_schur G hG00`. Establish `hN : G 0 0 = ((‖u y‖ ^ 2 : ℝ) : ℂ)`. Simplify using `[hG_def, hw]`. Establish `hNpos : 0 < ‖u y‖` using `norm_pos_iff.2 hu0`.

Unfold `maDensity`. Rewrite using `[hφ, ChartGram.mixedDisc_const, hcx, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin, hgram, hS]`. Generalize the expression as in `(Matrix.of fun i j : Fin e => G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0).det = Z`. Rewrite using `[hN]`. Establish `hnorm : ‖WithLp.toLp 2 (v y)‖ = ‖u y‖` using `rfl`.

Rewrite using `[hnorm]`. Generalize the expression as in `‖u y‖ = r at hNpos ⊢`. Rewrite using `[show ((2 : ℂ) * ((r ^ 2 : ℝ) : ℂ))⁻¹ ^ e = (((2 * r ^ 2)⁻¹ ^ e : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul, Complex.re_ofReal_mul, pow_mul]`. Establish `hpi : Real.pi ^ e * Real.pi⁻¹ ^ e = 1`. Rewrite using `[← mul_pow, mul_inv_cancel₀ Real.pi_ne_zero, one_pow]`.

Establish `hr : r ^ (e * 2) * r⁻¹ ^ (e * 2) = 1`. Rewrite using `[← mul_pow, mul_inv_cancel₀ hNpos.ne', one_pow]`. Establish `h2 : (1 / 2 : ℝ) ^ e * 2 ^ e = 1`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(r ^ 2 * Z.re * r ^ (e * 2) * r⁻¹ ^ (e * 2) * (1 / 2) ^ e * 2 ^ e) * hpi + (r ^ 2 * Z.re * (1 / 2) ^ e * 2 ^ e) * hr + (r ^ 2 * Z.re) * h2`.
-/
theorem ChartGramMA.proof : ChartGramMA.Statement := by
  intro e n v y hv h0

  obtain ⟨t, ht, hto, hyt⟩ := eventually_nhds_iff.1 hv
  have han : AnalyticOnNhd ℂ v t := by
    have hd : DifferentiableOn ℂ v t := fun y' hy' => (ht y' hy').differentiableWithinAt
    exact AnalyticOnNhd.pi fun j =>
      ReciprocityTheory.AnForm.Osgood.osgood e t _ hto (differentiableOn_pi.mp hd j)
  set L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm with hL
  set u : (Fin e → ℂ) → EuclideanSpace ℂ (Fin n) := fun y' => L (v y') with hu_def
  have hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y' := by
    filter_upwards [hto.mem_nhds hyt] with y' hy'
    exact (L : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).analyticAt _ |>.comp (han y' hy')
  have hu0 : u y ≠ 0 := by
    simpa [hu_def, hL, PiLp.coe_symm_continuousLinearEquiv] using h0
  have hDu : ∀ b, fderiv ℂ u y b = L (fderiv ℂ v y b) := fun b => by
    have hc := (L : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).hasFDerivAt.comp y
      (hv.self_of_nhds).hasFDerivAt
    have hc' : HasFDerivAt u _ y := hc
    rw [hc'.fderiv]
    rfl

  have hφ : (fun (_ : Fin e) (y' : Fin e → ℂ) => Real.log ‖WithLp.toLp 2 (v y')‖) =
      fun _ y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re := by
    funext _ y'
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (u y')
    have h' : (⟪u y', u y'⟫_ℂ).re = ‖u y'‖ ^ 2 := h
    rw [h', Real.log_pow]
    simp [hu_def, hL]

  set w : Fin (e + 1) → EuclideanSpace ℂ (Fin n) :=
    Fin.cons (u y) fun j => fderiv ℂ u y (Pi.single j 1) with hw
  set G : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := Matrix.of fun a b => ⟪w a, w b⟫_ℂ with hG_def
  have hmat : G = Matrix.of fun a b => ∑ i,
      star ((Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) a i) *
        (Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) b i := by
    ext a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp only [hG_def, hw, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, hDu] <;>
      simp only [PiLp.inner_apply, RCLike.inner_apply'] <;>
      simp [hu_def, hL]
  have hgram : gramVol v y = G.det.re := by
    rw [hmat]; rfl
  have hG00 : G 0 0 ≠ 0 := by
    simpa [hG_def, hw] using hu0
  have hcx : cxHessian (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y =
      (2 * G 0 0)⁻¹ • Matrix.transpose (Matrix.of fun i j : Fin e =>
        G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0) := by
    ext i j
    rw [ChartGram.cxHessian_half_log hu hu0]
    simp only [hG_def, hw, Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Fin.cons_zero, Fin.cons_succ, smul_eq_mul]
    have : ⟪u y, u y⟫_ℂ ≠ 0 := by simpa [hG_def, hw] using hG00
    field_simp
  have hS := ChartGram.det_eq_corner_mul_schur G hG00
  have hN : G 0 0 = ((‖u y‖ ^ 2 : ℝ) : ℂ) := by
    simp [hG_def, hw]
  have hNpos : 0 < ‖u y‖ := norm_pos_iff.2 hu0
  unfold maDensity
  rw [hφ, ChartGram.mixedDisc_const, hcx, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin,
    hgram, hS]
  generalize (Matrix.of fun i j : Fin e => G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0).det = Z
  rw [hN]
  have hnorm : ‖WithLp.toLp 2 (v y)‖ = ‖u y‖ := rfl
  rw [hnorm]
  generalize ‖u y‖ = r at hNpos ⊢
  rw [show ((2 : ℂ) * ((r ^ 2 : ℝ) : ℂ))⁻¹ ^ e = (((2 * r ^ 2)⁻¹ ^ e : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul, pow_mul]
  have hpi : Real.pi ^ e * Real.pi⁻¹ ^ e = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ Real.pi_ne_zero, one_pow]
  have hr : r ^ (e * 2) * r⁻¹ ^ (e * 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hNpos.ne', one_pow]
  have h2 : (1 / 2 : ℝ) ^ e * 2 ^ e = 1 := by
    rw [← mul_pow]; norm_num
  field_simp
  linear_combination (r ^ 2 * Z.re * r ^ (e * 2) * r⁻¹ ^ (e * 2) * (1 / 2) ^ e * 2 ^ e) * hpi +
    (r ^ 2 * Z.re * (1 / 2) ^ e * 2 ^ e) * hr + (r ^ 2 * Z.re) * h2

end GroundTheory.Heights₂.Heights
