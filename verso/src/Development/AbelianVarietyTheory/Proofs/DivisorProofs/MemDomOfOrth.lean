import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc

noncomputable section

namespace GlobalTheory.SUChartSection

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def gsU (X : Data E r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  FrameDegreeData.uMat (PoinPf.Gw X w τ)

def gsS (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (k : Fin r) : ℝ :=
  (Real.sqrt |(((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re|)⁻¹

def gsB (X : Data E r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  gsU X w τ * Matrix.diagonal fun k => ((gsS X w τ k : ℝ) : ℂ)

def yM (X : Data E r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  mat (nmat X w) τ * gsB X w τ

def yF (X : Data E r) (w : V (nd X)) : X.Ψ → Fin r → Fin r → ℂ := fun τ a b => yM X w τ a b

def dY (X : Data E r) : V (nd X) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ) := fderiv ℝ (yF X) 0

def secM (X : Data E r) (x : Frame X.Ψ r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  mat x τ * yM X w τ * (mat x τ)⁻¹

/- English proof (translation)
Use `show gram τ.1 X.Gm (mat x τ * mat (nmat X w) τ) = _`. Rewrite using `[FrameDegreeData.gram_mul, hx τ]`. Both sides reduce to the same expression.
-/
theorem gram_cpt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (cpt X x w) τ) = PoinPf.Gw X w τ := by
  show gram τ.1 X.Gm (mat x τ * mat (nmat X w) τ) = _
  rw [FrameDegreeData.gram_mul, hx τ]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Simplify using `only [FrameDegreeData.bOf, FrameDegreeData.uOf, gram_cpt X hx, gsB, gsU]`. Use `congrArg (fun d => FrameDegreeData.uMat (PoinPf.Gw X w τ) * Matrix.diagonal d) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Simplify using `only [FrameDegreeData.sOf, FrameDegreeData.dOf, FrameDegreeData.uOf, FrameDegreeData.gram_mul, gram_cpt X hx, gsS, gsU]`.
-/
theorem bOf_cpt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) :
    FrameDegreeData.bOf X (cpt X x w) = fun τ => gsB X w τ := by
  funext τ
  simp only [FrameDegreeData.bOf, FrameDegreeData.uOf, gram_cpt X hx, gsB, gsU]
  refine congrArg (fun d => FrameDegreeData.uMat (PoinPf.Gw X w τ) * Matrix.diagonal d) ?_
  funext k
  simp only [FrameDegreeData.sOf, FrameDegreeData.dOf, FrameDegreeData.uOf, FrameDegreeData.gram_mul, gram_cpt X hx, gsS, gsU]

/- English proof (translation)
Introduce `h0`. Establish `h1` using `congrArg Matrix.det (hx τ)`. Rewrite `h1` using `[FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul, Matrix.det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h1.symm` and prove the remaining obligations. Conclude with `PoinPf.sgn_ne _ _` after adjusting the coercions.
-/
theorem det_ne_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det (hx τ)
  rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at h1
  refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h1.symm
  exact_mod_cast PoinPf.sgn_ne _ _

/- English proof (translation)
Introduce `τ`. Use `⟨det_ne_of_orth X hx τ, fun i => ?_⟩` and prove the remaining obligations. Establish `h` using `PoinPf.dmin_cpt_orth X hx 0 τ i`. Rewrite `h` using `[PoinPf.cpt_zero, PoinPf.Gw_zero, PoinPf.lminor_Jd]`. Rewrite using `[h, Complex.ofReal_re]`.

Conclude with `mul_self_pos.2 (PoinPf.psgn_ne _ _)`.
-/
theorem mem_dom_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) : x ∈ X.dom := by
  intro τ
  refine ⟨det_ne_of_orth X hx τ, fun i => ?_⟩
  have h := PoinPf.dmin_cpt_orth X hx 0 τ i
  rw [PoinPf.cpt_zero, PoinPf.Gw_zero, PoinPf.lminor_Jd] at h
  rw [h, Complex.ofReal_re]
  exact mul_self_pos.2 (PoinPf.psgn_ne _ _)

/- English proof (translation)
Take `⟨R, hR, h⟩` from `PoinPf.good_ball X 0`. Conclude with `⟨R, hR, fun w hw => PoinPf.cpt_mem_dom X (mem_dom_of_orth X hx) hx (h w hw).1 (h w hw).2.1⟩`.
-/
theorem exists_ball (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) :
    ∃ R > 0, ∀ w ∈ Metric.ball (0 : V (nd X)) R, cpt X x w ∈ X.dom := by
  obtain ⟨R, hR, h⟩ := PoinPf.good_ball X 0
  exact ⟨R, hR, fun w hw => PoinPf.cpt_mem_dom X (mem_dom_of_orth X hx) hx (h w hw).1 (h w hw).2.1⟩

/- English proof (translation)
Use extensionality with `j c`. Simplify using `only [gsU, PoinPf.Gw_zero, FrameDegreeData.uMat, Matrix.of_apply, Matrix.one_apply]`. Use `split_ifs with h1 h2`. Both sides reduce to the same expression. Establish `: FrameDegreeData.rowc (PoinPf.Jd X) c = 0`.

Use function extensionality and compare the values at `m`. Simplify using `only [FrameDegreeData.rowc, PoinPf.Jd, Pi.zero_apply]`. Rewrite using `[Matrix.diagonal_apply_ne]`. Introduce `hc`. Establish `: ((Fin.castLE c.isLt.le m : Fin r) : ℕ) < c` using `m.isLt`.

Rewrite `this` using `[← hc]`. Conclude with `lt_irrefl _ this`. Rewrite using `[this, Matrix.zero_vecMul, Pi.zero_apply, neg_zero]`. Both sides reduce to the same expression.
-/
theorem gsU_zero (X : Data E r) (τ : X.Ψ) : gsU X 0 τ = 1 := by
  ext j c
  simp only [gsU, PoinPf.Gw_zero, FrameDegreeData.uMat, Matrix.of_apply, Matrix.one_apply]
  split_ifs with h1 h2
  · rfl
  · have : FrameDegreeData.rowc (PoinPf.Jd X) c = 0 := by
      funext m
      simp only [FrameDegreeData.rowc, PoinPf.Jd, Pi.zero_apply]
      rw [Matrix.diagonal_apply_ne]
      intro hc
      have : ((Fin.castLE c.isLt.le m : Fin r) : ℕ) < c := m.isLt
      rw [← hc] at this
      exact lt_irrefl _ this
    rw [this, Matrix.zero_vecMul, Pi.zero_apply, neg_zero]
  · rfl

/- English proof (translation)
Establish `hS : ∀ k, gsS X 0 τ k = 1`. Introduce `k`. Simplify using `only [gsS, gsU_zero, Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, PoinPf.Gw_zero, PoinPf.Jd, Matrix.diagonal_apply_eq, Complex.ofReal_re, PoinPf.abs_sgn, Real.sqrt_one, inv_one]`. Rewrite using `[gsB, gsU_zero, Matrix.one_mul]`. Simplify using `only [hS, Complex.ofReal_one, Matrix.diagonal_one]`.
-/
theorem gsB_zero (X : Data E r) (τ : X.Ψ) : gsB X 0 τ = 1 := by
  have hS : ∀ k, gsS X 0 τ k = 1 := by
    intro k
    simp only [gsS, gsU_zero, Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.mul_one, PoinPf.Gw_zero, PoinPf.Jd, Matrix.diagonal_apply_eq, Complex.ofReal_re, PoinPf.abs_sgn,
      Real.sqrt_one, inv_one]
  rw [gsB, gsU_zero, Matrix.one_mul]
  simp only [hS, Complex.ofReal_one, Matrix.diagonal_one]

/- English proof (translation)
Rewrite using `[yM, PoinPf.nmat_zero, gsB_zero, Matrix.one_mul]`.
-/
theorem yM_zero (X : Data E r) (τ : X.Ψ) : yM X 0 τ = 1 := by
  rw [yM, PoinPf.nmat_zero, gsB_zero, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[secM, yM_zero, Matrix.mul_one, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ))]`.
-/
theorem secM_zero (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) : secM X x 0 τ = 1 := by
  rw [secM, yM_zero, Matrix.mul_one, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ))]

/- English proof (translation)
Rewrite using `[gsB, Matrix.mul_diagonal, gsU, FrameDegreeData.uMat_upper _ h, zero_mul]`.
-/
theorem gsB_lower (X : Data E r) (w : V (nd X)) (τ : X.Ψ) {a b : Fin r} (h : b < a) : gsB X w τ a b = 0 := by
  rw [gsB, Matrix.mul_diagonal, gsU, FrameDegreeData.uMat_upper _ h, zero_mul]

/- English proof (translation)
Rewrite using `[gsB, Matrix.mul_diagonal, gsU, FrameDegreeData.uMat_diag, one_mul]`.
-/
theorem gsB_diag (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (a : Fin r) :
    gsB X w τ a a = ((gsS X w τ a : ℝ) : ℂ) := by
  rw [gsB, Matrix.mul_diagonal, gsU, FrameDegreeData.uMat_diag, one_mul]

end GlobalTheory.SUChartSection
