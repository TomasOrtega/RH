import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Finset PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open scoped ContDiff ComplexConjugate InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WeightIbp

variable {n : ℕ}

/- English proof (translation)
Establish `h : Continuous fun g : Mat n => g.det` using `Continuous.matrix_det continuous_id`. Conclude with `isOpen_ne_fun h continuous_const`.
-/
theorem isOpen_invertible : IsOpen (GLs n) := by
  have h : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun h continuous_const

/- English proof (translation)
Establish `h : y.val.det * (y⁻¹ : G n).val.det = 1`. Rewrite using `[← Matrix.det_mul, Units.mul_inv, Matrix.det_one]`. Conclude with `left_ne_zero_of_mul_eq_one h`.
-/
theorem val_mem_invertible (y : G n) : y.val ∈ GLs n := by
  have h : y.val.det * (y⁻¹ : G n).val.det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  exact left_ne_zero_of_mul_eq_one h

/- English proof (translation)
Take `⟨R, hR⟩` from `hc`. Establish `hcont : Continuous fun y : G n => F y.val` using `hF.comp_continuous Units.continuous_val val_mem_invertible`. Establish `hK : IsCompact {y : G n | lg y.val ≤ R}` using `(hL n).2.2.2.2.1 R`. Establish `hsupp : HasCompactSupport fun y : G n => F y.val`. Use `HasCompactSupport.intro hK fun y hy => ?_` and prove the remaining obligations.

Conclude with `hR _ (val_mem_invertible y) (not_le.1 hy)`. Conclude with `hcont.integrable_of_hasCompactSupport hsupp`.
-/
theorem integrable_of_continuousOn (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] {W : Type} [NormedAddCommGroup W] (F : Mat n → W) (hF : ContinuousOn F (GLs n)) (hc : Cpt F) :
    Integrable (fun y : G n => F y.val) μ := by
  obtain ⟨R, hR⟩ := hc
  have hcont : Continuous fun y : G n => F y.val :=
    hF.comp_continuous Units.continuous_val val_mem_invertible
  have hK : IsCompact {y : G n | lg y.val ≤ R} := (hL n).2.2.2.2.1 R
  have hsupp : HasCompactSupport fun y : G n => F y.val := by
    refine HasCompactSupport.intro hK fun y hy => ?_
    exact hR _ (val_mem_invertible y) (not_le.1 hy)
  exact hcont.integrable_of_hasCompactSupport hsupp

/- English proof (translation)
Establish `hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)` using `(hL n).2.2.2.1.continuousOn`. Establish `hU : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi R)` using `hlg.isOpen_inter_preimage isOpen_invertible isOpen_Ioi`. Establish `he : φ =ᶠ[nhds y] fun _ => (0 : ℝ)` using `Filter.eventuallyEq_of_mem (hU.mem_nhds ⟨hy, hl⟩) fun z hz => hR z hz.1 hz.2`. Rewrite using `[he.fderiv_eq]`. Conclude with `fderiv_const_apply 0`.
-/
theorem fderiv_eq_zero_far (hL : LgFacts) {φ : Mat n → ℝ} {R : ℝ} (hR : ∀ y ∈ GLs n, R < lg y → φ y = 0)
    {y : Mat n} (hy : y ∈ GLs n) (hl : R < lg y) : fderiv ℝ φ y = 0 := by
  have hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n) := (hL n).2.2.2.1.continuousOn
  have hU : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi R) := hlg.isOpen_inter_preimage isOpen_invertible isOpen_Ioi
  have he : φ =ᶠ[nhds y] fun _ => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds ⟨hy, hl⟩) fun z hz => hR z hz.1 hz.2
  rw [he.fderiv_eq]
  exact fderiv_const_apply 0

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/- English proof (translation)
Establish `hn` using `isOpen_invertible.mem_nhds hy`. Establish `hfd : HasFDerivAt f (fderiv ℝ f y) y` using `((hf.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt`. Establish `hhd : HasFDerivAt h (fderiv ℝ h y) y` using `((hh.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt`. Establish `hφd : HasFDerivAt φ (fderiv ℝ φ y) y` using `((hφ.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt`. Establish `hi` using `hhd.inner ℂ hfd`.

Establish `ho` using `Complex.ofRealCLM.hasFDerivAt.comp y hφd`. Establish `hm` using `ho.mul hi`. Use `hm.fderiv` as an intermediate fact. Establish `key : fderiv ℝ (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) y (y * X) = (φ y : ℂ) * fderivInnerCLM ℂ (h y, f y) (fderiv ℝ h y (y * X), fderiv ℝ f y (y * X)) + ⟪h y, f y⟫_ℂ * (fderiv ℝ φ y (y * X) : ℂ)`. Establish `e : (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) = (⇑Complex.ofRealCLM ∘ φ * fun t => ⟪h t, f t⟫_ℂ)` using `rfl`.

Rewrite using `[e]`. Use `erw [this]`. Both sides reduce to the same expression. Simplify using `only [Rd]`. Rewrite using `[key, fderivInnerCLM_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem Rd_weight_inner {f h : Mat n → V} {φ : Mat n → ℝ} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hh : ContDiffOn ℝ ∞ h (GLs n)) (hφ : ContDiffOn ℝ ∞ φ (GLs n)) (X : Mat n) {y : Mat n} (hy : y ∈ GLs n) :
    Rd X (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) y =
      (φ y : ℂ) * ⟪h y, Rd X f y⟫_ℂ + (φ y : ℂ) * ⟪Rd X h y, f y⟫_ℂ +
        (fderiv ℝ φ y (y * X) : ℂ) * ⟪h y, f y⟫_ℂ := by
  have hn := isOpen_invertible.mem_nhds hy
  have hfd : HasFDerivAt f (fderiv ℝ f y) y :=
    ((hf.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hhd : HasFDerivAt h (fderiv ℝ h y) y :=
    ((hh.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hφd : HasFDerivAt φ (fderiv ℝ φ y) y :=
    ((hφ.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hi := hhd.inner ℂ hfd
  have ho := Complex.ofRealCLM.hasFDerivAt.comp y hφd
  have hm := ho.mul hi
  have := hm.fderiv
  have key : fderiv ℝ (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) y (y * X) =
      (φ y : ℂ) * fderivInnerCLM ℂ (h y, f y) (fderiv ℝ h y (y * X), fderiv ℝ f y (y * X)) +
        ⟪h y, f y⟫_ℂ * (fderiv ℝ φ y (y * X) : ℂ) := by
    have e : (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) = (⇑Complex.ofRealCLM ∘ φ * fun t => ⟪h t, f t⟫_ℂ) := rfl
    rw [e]
    erw [this]
    rfl
  simp only [Rd]
  rw [key, fderivInnerCLM_apply]
  ring

/- English proof (translation)
Introduce `hR hL n _ _ μ _ V _ _ f h φ hf hh hφ hc X`. Take `⟨R, hRφ⟩` from `id hc`. Establish `hφc : ContinuousOn (fun y => (φ y : ℂ)) (GLs n)` using `Complex.continuous_ofReal.comp_continuousOn hφ.continuousOn`. Establish `hFs : ContDiffOn ℝ ∞ (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) (GLs n)` using `(Complex.ofRealCLM.contDiff.comp_contDiffOn hφ).mul (hh.inner ℂ hf)`. Establish `hFc : Cpt (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ)` using `⟨R, fun y hy hl => by simp [hRφ y hy hl]⟩`.

Establish `h0` using `(hR n).2.2 μ ℂ _ hFs hFc X`. Establish `hRf` using `((hR n).1 V f hf).1 X`. Establish `hRh` using `((hR n).1 V h hh).1 X`. Establish `iA : Integrable (fun y : G n => (φ y.val : ℂ) * ⟪h y.val, Rd X f y.val⟫_ℂ) μ` using `integrable_of_continuousOn hL μ (fun z => (φ z : ℂ) * ⟪h z, Rd X f z⟫_ℂ) (hφc.mul (hh.continuousOn.inner hRf.continuousOn)) ⟨R, fun y hy hl => by simp [hRφ y hy hl]⟩`. Establish `iB : Integrable (fun y : G n => (φ y.val : ℂ) * ⟪Rd X h y.val, f y.val⟫_ℂ) μ` using `integrable_of_continuousOn hL μ (fun z => (φ z : ℂ) * ⟪Rd X h z, f z⟫_ℂ) (hφc.mul (hRh.continuousOn.inner hf.continuousOn)) ⟨R, fun y hy hl => by simp [hRφ y hy hl]⟩`.

Establish `hdc : ContinuousOn (fun y : Mat n => ((fderiv ℝ φ y (y * X) : ℝ) : ℂ)) (GLs n)`. Establish `h1 : ContinuousOn (fderiv ℝ φ) (GLs n)` using `hφ.continuousOn_fderiv_of_isOpen isOpen_invertible (by simp)`. Establish `h2 : ContinuousOn (fun y : Mat n => y * X) (GLs n)` using `(continuous_id.matrix_mul continuous_const).continuousOn`. Conclude with `Complex.continuous_ofReal.comp_continuousOn (h1.clm_apply h2)`. Establish `iC : Integrable (fun y : G n => (fderiv ℝ φ y.val (y.val * X) : ℂ) * ⟪h y.val, f y.val⟫_ℂ) μ` using `integrable_of_continuousOn hL μ (fun z => (fderiv ℝ φ z (z * X) : ℂ) * ⟪h z, f z⟫_ℂ) (hdc.mul (hh.continuousOn.inner hf.continuousOn)) ⟨R, fun y hy hl => by simp [fderiv_eq_zero_far hL hRφ hy hl]⟩`.

Establish `hsum : ∫ y : G n, Rd X (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) y.val ∂μ = (∫ y : G n, (φ y.val : ℂ) * ⟪h y.val, Rd X f y.val⟫_ℂ ∂μ) + (∫ y : G n, (φ y.val : ℂ) * ⟪Rd X h y.val, f y.val⟫_ℂ ∂μ) + ∫ y : G n, (fderiv ℝ φ y.val (y.val * X) : ℂ) * ⟪h y.val, f y.val⟫_ℂ ∂μ`. Establish `e` using `integral_add (iA.add iB) iC`. Simplify using `only [Pi.add_apply] at e`. Rewrite using `[← integral_add iA iB, ← e]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Conclude with `Rd_weight_inner hf hh hφ X (val_mem_invertible y)`. Rewrite `hsum` using `[h0]`. Take the linear combination `-hsum`.
-/
theorem weight_ibp : RCalc → LgFacts → ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (f h : Mat n → V) (φ : Mat n → ℝ), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → ContDiffOn ℝ ∞ φ (GLs n) → Cpt φ → ∀ X : Mat n, ∫ y : G n, (φ y.val : ℂ) * ⟪h y.val, Rd X f y.val⟫_ℂ ∂μ = -(∫ y : G n, (φ y.val : ℂ) * ⟪Rd X h y.val, f y.val⟫_ℂ ∂μ) - ∫ y : G n, (fderiv ℝ φ y.val (y.val * X) : ℂ) * ⟪h y.val, f y.val⟫_ℂ ∂μ := by
  intro hR hL n _ _ μ _ V _ _ f h φ hf hh hφ hc X
  obtain ⟨R, hRφ⟩ := id hc
  have hφc : ContinuousOn (fun y => (φ y : ℂ)) (GLs n) :=
    Complex.continuous_ofReal.comp_continuousOn hφ.continuousOn
  have hFs : ContDiffOn ℝ ∞ (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) (GLs n) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ).mul (hh.inner ℂ hf)
  have hFc : Cpt (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) :=
    ⟨R, fun y hy hl => by simp [hRφ y hy hl]⟩
  have h0 := (hR n).2.2 μ ℂ _ hFs hFc X
  have hRf := ((hR n).1 V f hf).1 X
  have hRh := ((hR n).1 V h hh).1 X
  have iA : Integrable (fun y : G n => (φ y.val : ℂ) * ⟪h y.val, Rd X f y.val⟫_ℂ) μ :=
    integrable_of_continuousOn hL μ (fun z => (φ z : ℂ) * ⟪h z, Rd X f z⟫_ℂ)
      (hφc.mul (hh.continuousOn.inner hRf.continuousOn)) ⟨R, fun y hy hl => by simp [hRφ y hy hl]⟩
  have iB : Integrable (fun y : G n => (φ y.val : ℂ) * ⟪Rd X h y.val, f y.val⟫_ℂ) μ :=
    integrable_of_continuousOn hL μ (fun z => (φ z : ℂ) * ⟪Rd X h z, f z⟫_ℂ)
      (hφc.mul (hRh.continuousOn.inner hf.continuousOn)) ⟨R, fun y hy hl => by simp [hRφ y hy hl]⟩
  have hdc : ContinuousOn (fun y : Mat n => ((fderiv ℝ φ y (y * X) : ℝ) : ℂ)) (GLs n) := by
    have h1 : ContinuousOn (fderiv ℝ φ) (GLs n) :=
      hφ.continuousOn_fderiv_of_isOpen isOpen_invertible (by simp)
    have h2 : ContinuousOn (fun y : Mat n => y * X) (GLs n) :=
      (continuous_id.matrix_mul continuous_const).continuousOn
    exact Complex.continuous_ofReal.comp_continuousOn (h1.clm_apply h2)
  have iC : Integrable (fun y : G n => (fderiv ℝ φ y.val (y.val * X) : ℂ) * ⟪h y.val, f y.val⟫_ℂ) μ :=
    integrable_of_continuousOn hL μ (fun z => (fderiv ℝ φ z (z * X) : ℂ) * ⟪h z, f z⟫_ℂ)
      (hdc.mul (hh.continuousOn.inner hf.continuousOn))
      ⟨R, fun y hy hl => by simp [fderiv_eq_zero_far hL hRφ hy hl]⟩
  have hsum : ∫ y : G n, Rd X (fun z => (φ z : ℂ) * ⟪h z, f z⟫_ℂ) y.val ∂μ =
      (∫ y : G n, (φ y.val : ℂ) * ⟪h y.val, Rd X f y.val⟫_ℂ ∂μ) +
        (∫ y : G n, (φ y.val : ℂ) * ⟪Rd X h y.val, f y.val⟫_ℂ ∂μ) +
        ∫ y : G n, (fderiv ℝ φ y.val (y.val * X) : ℂ) * ⟪h y.val, f y.val⟫_ℂ ∂μ := by
    have e := integral_add (iA.add iB) iC
    simp only [Pi.add_apply] at e
    rw [← integral_add iA iB, ← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact Rd_weight_inner hf hh hφ X (val_mem_invertible y)
  rw [h0] at hsum
  linear_combination -hsum

end GlobalTheory.CompanionTheory.WeightIbp
