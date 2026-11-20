import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnGramSchmidtUpperTriangularFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetUnitaryChartSectionConjugatedMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHermitianFormUnitaryChartSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesHasStrictFDerivAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFderivBelowDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivSkewStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivDiagImStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSkewMemProductSpecialUnitaryLieAlgebraStatement

noncomputable section

namespace GlobalTheory.SUChartSection
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal ComplexConjugate ContDiff

/- English proof (translation)
Introduce `E _ _ _ r X x hx`. Take `⟨R, hR, hball⟩` from `exists_ball X hx`. Establish `hdet1 : ∀ w, cpt X x w ∈ X.dom → ∀ τ, (secM X x w τ).det ≠ 0` using `fun w hw τ => by`. Rewrite using `[GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix X hx hw τ]`. Conclude with `one_ne_zero`.

Set `secU : ∀ w, cpt X x w ∈ X.dom → realSU X.Ψ X.Gm` to `fun w hw => ⟨fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (secM X x w τ) (hdet1 w hw τ), fun τ => ⟨GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix X hx hw τ, GlobalTheory.T.complexHermitianForm_unitaryChartSection X hx hw τ⟩⟩`. Establish `hsecU : ∀ w (hw : cpt X x w ∈ X.dom) τ, ((((secU w hw : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = secM X x w τ` using `fun _ _ _ => rfl`. Set `σ : V (nd X) → realSU X.Ψ X.Gm` to `fun w => if h : w ∈ Metric.ball (0 : V (nd X)) R then secU w (hball w h) else 1`. Establish `hσ : ∀ w (h : w ∈ Metric.ball (0 : V (nd X)) R) τ, ((((σ w : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = secM X x w τ` using `fun w h τ => by`. Simplify using `only [σ, dif_pos h]`.

Both sides reduce to the same expression. Establish `hx0 : ∀ τ, IsUnit (mat x τ).det` using `fun τ => isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)`. Establish `h0 : (0 : V (nd X)) ∈ Metric.ball (0 : V (nd X)) R` using `Metric.mem_ball_self hR`. Set `Cx : (X.Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → Fin r → ℂ)` to `{ toFun := fun Y τ => (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) map_add' := fun Y Z => by`. Use function extensionality and compare the values at `τ`.

Establish `e : Matrix.of ((Y + Z) τ) = Matrix.of (Y τ) + Matrix.of (Z τ)` using `rfl`. Simplify using `only [e, Matrix.mul_add, Matrix.add_mul]`. Both sides reduce to the same expression. Use the proof step `map_smul' := fun c Y => by`. Use function extensionality and compare the values at `τ`.

Establish `e : Matrix.of ((c • Y) τ) = c • Matrix.of (Y τ)` using `rfl`. Simplify using `only [e, Matrix.mul_smul, Matrix.smul_mul]`. Use `rfl }`. Set `C` to `LinearMap.toContinuousLinearMap Cx`. Establish `hC : ∀ Y τ, C Y τ = (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)` using `fun _ _ => rfl`.

Use `⟨σ, R, C.comp (dY X), hR, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Subtype.ext (funext fun τ => Units.ext ?_)` and prove the remaining obligations. Rewrite using `[hσ 0 h0 τ, secM_zero X hx τ]`. Both sides reduce to the same expression. Rewrite using `[continuousOn_iff_continuous_restrict]`.

Establish `hg : ∀ τ, Continuous fun w : Metric.ball (0 : V (nd X)) R => gsB X w τ` using `fun τ => by`. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Conclude with `((GlobalTheory.T.contDiffOn_gramSchmidtUpperTriangularFactor X hx τ a b).continuousOn.mono (fun w hw => hball w hw)).restrict`. Establish `hM : ∀ τ, Continuous fun w : Metric.ball (0 : V (nd X)) R => secM X x w τ` using `fun τ => by`. Use `(continuous_const.matrix_mul ?_).matrix_mul continuous_const` and prove the remaining obligations.

Conclude with `((PoinPf.cont_nmatm X τ).comp continuous_subtype_val).matrix_mul (hg τ)`. Use `continuous_induced_rng.2 (continuous_pi fun τ => Units.continuous_iff.2 ⟨?_, ?_⟩)` and prove the remaining obligations. Use `(hM τ).congr fun w => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Set.restrict_apply]`. Conclude with `(hσ w w.2 τ).symm`.

Use `((hM τ).matrix_adjugate).congr fun w => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Set.restrict_apply]`. Rewrite using `[Matrix.coe_units_inv, hσ w w.2 τ, Matrix.inv_def, GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix X hx (hball w w.2) τ, Ring.inverse_one, one_smul]`. Introduce `z hz`. Use `⟨FrameDegreeData.bOf X (cpt X x z), FrameDegreeData.bOf_mem X (hball z hz), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `τ`. Use `show (((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ : Matrix (Fin r) (Fin r) ℂ) = (mat (cpt X x z) τ * mat (FrameDegreeData.bOf X (cpt X x z)) τ : Matrix (Fin r) (Fin r) ℂ)`. Rewrite using `[hσ z hz τ, bOf_cpt X hx z]`. Use `show mat x τ * yM X z τ * (mat x τ)⁻¹ * mat x τ = mat x τ * mat (nmat X z) τ * gsB X z τ`. Rewrite using `[Matrix.mul_assoc _ (mat x τ)⁻¹, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.mul_one, yM, Matrix.mul_assoc]`.

Establish `h1 : HasStrictFDerivAt (fun z => C (yF X z)) (C.comp (dY X)) 0` using `C.hasStrictFDerivAt.comp 0 (GlobalTheory.T.unitaryChartSectionFrameEntries_hasStrictFDerivAt X hx)`. Use `h1.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [Metric.ball_mem_nhds (0 : V (nd X)) hR] with z hz`. Use function extensionality and compare the values at `τ a b`. Rewrite using `[hσ z hz τ, hC]`.

Both sides reduce to the same expression. Introduce `z`. Establish `hdiag : ∀ τ a, dY X z τ a a = 0` using `fun τ a => by`. Establish `h6` using `congrArg Complex.re (GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_skew X hx z τ a a)`. Establish `h7` using `GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_diag_im X hx z τ a`.

Simplify using `only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, h7, Complex.zero_re, mul_zero, sub_zero, zero_mul, neg_zero] at h6`. Establish `hs` using `PoinPf.sgn_ne X.p0 (a : ℕ)`. Establish `hre : (dY X z τ a a).re = 0`. Establish `: 2 * sgn X.p0 (a : ℕ) * (dY X z τ a a).re = 0` using `by linarith`. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Conclude with `absurd (by linarith : sgn X.p0 (a : ℕ) = 0) hs`. Conclude with `h`. Conclude with `Complex.ext hre h7`. Establish `hIF : ∀ τ, inFrame x (C.comp (dY X) z) τ = Matrix.of (dY X z τ)` using `fun τ => by show (mat x τ)⁻¹ * Matrix.of (C (dY X z) τ) * mat x τ = _`. Rewrite using `[hC]`.

Use `show (mat x τ)⁻¹ * (mat x τ * Matrix.of (dY X z τ) * (mat x τ)⁻¹) * mat x τ = _`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.mul_one]`. Use `⟨?_, fun τ a b h => ?_, fun τ a => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.T.conj_skew_mem_productSpecialUnitaryLieAlgebra X hx (fun τ => Matrix.of (dY X z τ)) (fun τ a b => GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_skew X hx z τ a b) hdiag`. Rewrite using `[hIF]`.

Conclude with `GlobalTheory.T.unitaryChartSection_fderiv_below_diagonal X hx z τ a b h`. Rewrite using `[hIF]`. Conclude with `hdiag τ a`.
-/
theorem exists_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (σ : V (nd X) → realSU X.Ψ X.Gm) (ρ : ℝ) (D₁ : V (nd X) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), 0 < ρ ∧ σ 0 = 1 ∧ ContinuousOn σ (Metric.ball 0 ρ) ∧ (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) ∧ HasStrictFDerivAt (fun z => (fun τ a b => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) D₁ 0 ∧ ∀ z, D₁ z ∈ realLie X.Ψ X.Gm ∧ (∀ τ a b, b < a → inFrame x (D₁ z) τ a b = nmat X z τ a b) ∧ ∀ τ a, inFrame x (D₁ z) τ a a = 0 := by
  intro E _ _ _ r X x hx
  classical
  obtain ⟨R, hR, hball⟩ := exists_ball X hx
  have hdet1 : ∀ w, cpt X x w ∈ X.dom → ∀ τ, (secM X x w τ).det ≠ 0 := fun w hw τ => by
    rw [GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix X hx hw τ]; exact one_ne_zero
  let secU : ∀ w, cpt X x w ∈ X.dom → realSU X.Ψ X.Gm := fun w hw =>
    ⟨fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (secM X x w τ) (hdet1 w hw τ),
      fun τ => ⟨GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix X hx hw τ, GlobalTheory.T.complexHermitianForm_unitaryChartSection X hx hw τ⟩⟩
  have hsecU : ∀ w (hw : cpt X x w ∈ X.dom) τ,
      ((((secU w hw : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        secM X x w τ := fun _ _ _ => rfl
  let σ : V (nd X) → realSU X.Ψ X.Gm := fun w => if h : w ∈ Metric.ball (0 : V (nd X)) R then secU w (hball w h) else 1
  have hσ : ∀ w (h : w ∈ Metric.ball (0 : V (nd X)) R) τ,
      ((((σ w : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        secM X x w τ := fun w h τ => by
    simp only [σ, dif_pos h]; rfl
  have hx0 : ∀ τ, IsUnit (mat x τ).det := fun τ => isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  have h0 : (0 : V (nd X)) ∈ Metric.ball (0 : V (nd X)) R := Metric.mem_ball_self hR
  let Cx : (X.Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → Fin r → ℂ) :=
    { toFun := fun Y τ => (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
      map_add' := fun Y Z => by
        funext τ
        have e : Matrix.of ((Y + Z) τ) = Matrix.of (Y τ) + Matrix.of (Z τ) := rfl
        simp only [e, Matrix.mul_add, Matrix.add_mul]; rfl
      map_smul' := fun c Y => by
        funext τ
        have e : Matrix.of ((c • Y) τ) = c • Matrix.of (Y τ) := rfl
        simp only [e, Matrix.mul_smul, Matrix.smul_mul]; rfl }
  let C := LinearMap.toContinuousLinearMap Cx
  have hC : ∀ Y τ, C Y τ = (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) := fun _ _ => rfl
  refine ⟨σ, R, C.comp (dY X), hR, ?_, ?_, ?_, ?_, ?_⟩
  · refine Subtype.ext (funext fun τ => Units.ext ?_)
    rw [hσ 0 h0 τ, secM_zero X hx τ]; rfl
  · rw [continuousOn_iff_continuous_restrict]
    have hg : ∀ τ, Continuous fun w : Metric.ball (0 : V (nd X)) R => gsB X w τ := fun τ => by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      exact ((GlobalTheory.T.contDiffOn_gramSchmidtUpperTriangularFactor X hx τ a b).continuousOn.mono (fun w hw => hball w hw)).restrict
    have hM : ∀ τ, Continuous fun w : Metric.ball (0 : V (nd X)) R => secM X x w τ := fun τ => by
      refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
      exact ((PoinPf.cont_nmatm X τ).comp continuous_subtype_val).matrix_mul (hg τ)
    refine continuous_induced_rng.2 (continuous_pi fun τ => Units.continuous_iff.2 ⟨?_, ?_⟩)
    · refine (hM τ).congr fun w => ?_
      simp only [Function.comp_apply, Set.restrict_apply]
      exact (hσ w w.2 τ).symm
    · refine ((hM τ).matrix_adjugate).congr fun w => ?_
      simp only [Function.comp_apply, Set.restrict_apply]
      rw [Matrix.coe_units_inv, hσ w w.2 τ, Matrix.inv_def, GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix X hx (hball w w.2) τ, Ring.inverse_one, one_smul]
  · intro z hz
    refine ⟨FrameDegreeData.bOf X (cpt X x z), FrameDegreeData.bOf_mem X (hball z hz), ?_⟩
    funext τ
    show (((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ :
      Matrix (Fin r) (Fin r) ℂ) = (mat (cpt X x z) τ * mat (FrameDegreeData.bOf X (cpt X x z)) τ : Matrix (Fin r) (Fin r) ℂ)
    rw [hσ z hz τ, bOf_cpt X hx z]
    show mat x τ * yM X z τ * (mat x τ)⁻¹ * mat x τ = mat x τ * mat (nmat X z) τ * gsB X z τ
    rw [Matrix.mul_assoc _ (mat x τ)⁻¹, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.mul_one, yM, Matrix.mul_assoc]
  · have h1 : HasStrictFDerivAt (fun z => C (yF X z)) (C.comp (dY X)) 0 :=
      C.hasStrictFDerivAt.comp 0 (GlobalTheory.T.unitaryChartSectionFrameEntries_hasStrictFDerivAt X hx)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : V (nd X)) hR] with z hz
    funext τ a b
    rw [hσ z hz τ, hC]
    rfl
  · intro z
    have hdiag : ∀ τ a, dY X z τ a a = 0 := fun τ a => by
      have h6 := congrArg Complex.re (GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_skew X hx z τ a a)
      have h7 := GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_diag_im X hx z τ a
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
        Complex.conj_im, h7, Complex.zero_re, mul_zero, sub_zero, zero_mul, neg_zero] at h6
      have hs := PoinPf.sgn_ne X.p0 (a : ℕ)
      have hre : (dY X z τ a a).re = 0 := by
        have : 2 * sgn X.p0 (a : ℕ) * (dY X z τ a a).re = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (by linarith : sgn X.p0 (a : ℕ) = 0) hs
        · exact h
      exact Complex.ext hre h7
    have hIF : ∀ τ, inFrame x (C.comp (dY X) z) τ = Matrix.of (dY X z τ) := fun τ => by
      show (mat x τ)⁻¹ * Matrix.of (C (dY X z) τ) * mat x τ = _
      rw [hC]
      show (mat x τ)⁻¹ * (mat x τ * Matrix.of (dY X z τ) * (mat x τ)⁻¹) * mat x τ = _
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.one_mul,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.mul_one]
    refine ⟨?_, fun τ a b h => ?_, fun τ a => ?_⟩
    · exact GlobalTheory.T.conj_skew_mem_productSpecialUnitaryLieAlgebra X hx (fun τ => Matrix.of (dY X z τ)) (fun τ a b => GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_skew X hx z τ a b) hdiag
    · rw [hIF]; exact GlobalTheory.T.unitaryChartSection_fderiv_below_diagonal X hx z τ a b h
    · rw [hIF]; exact hdiag τ a
end GlobalTheory.SUChartSection
