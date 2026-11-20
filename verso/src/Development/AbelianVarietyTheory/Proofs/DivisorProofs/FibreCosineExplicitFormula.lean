import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsOne
open MeasureTheory
open scoped ComplexOrder ENNReal

set_option autoImplicit false

namespace GlobalTheory.FibCos

/- English proof (translation)
Establish `h00 : (0 : ℂ) < G 0 0` using `hG.diag_pos`. Establish `hdet : (0 : ℂ) < G.det` using `hG.det_pos`. Take `⟨ha, ha'⟩` from `Complex.pos_iff.mp h00`. Take `⟨hD, -⟩` from `Complex.pos_iff.mp hdet`. Establish `h01 : G 0 1 = (starRingEnd ℂ) (G 1 0)` using `(hG.isHermitian.apply 0 1).symm`.

Use `set a : ℝ := (G 0 0).re with ha_def`. Use `set D : ℝ := G.det.re with hD_def`. Establish `hGa : G 0 0 = (a : ℂ)`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[ha_def]`.

Simplify using `[← ha']`. Establish `haC : (a : ℂ) ≠ 0` using `by exact_mod_cast ha.ne'`. Use `set u : ℝ := ‖1 + G 1 0 / G 0 0 * x‖ ^ 2 with hu_def`. Use `set s : ℝ := ‖x‖ ^ 2 with hs_def`. Establish `hu : 0 < u` using `by positivity`.

Establish `hs : 0 ≤ s` using `by positivity`. Establish `hnum : ‖G 0 0 + x * G 1 0‖ ^ 2 = a ^ 2 * u`. Establish `: G 0 0 + x * G 1 0 = (a : ℂ) * (1 + G 1 0 / G 0 0 * x)`. Rewrite using `[hGa]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Establish `hDe : D = a * (G 1 1).re - ((G 1 0).re ^ 2 + (G 1 0).im ^ 2)`. Rewrite using `[hD_def, Matrix.det_fin_two, h01, hGa]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Establish `hn : nrm G x = a * u + D / a * s`. Establish `h1 : a * nrm G x = a ^ 2 * u + D * s`. Rewrite using `[← hnum, hDe, hs_def, nrm, h01, hGa]`. Simplify using `only [Complex.sq_norm, Complex.normSq_apply]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc : ‖(Real.sqrt D / a : ℂ)‖ ^ 2 = D / a ^ 2`. Rewrite using `[norm_div, div_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, Real.sq_sqrt hD.le]`.

Establish `hy : ‖(Real.sqrt D / a : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2 = D / a ^ 2 * s / u`. Rewrite using `[norm_div, norm_mul, div_pow, mul_pow, hc]`. Establish `hd : ‖(Real.sqrt D / a : ℂ) / (1 + G 1 0 / G 0 0 * x) ^ 2‖ ^ 2 = D / a ^ 2 / u ^ 2`. Rewrite using `[norm_div, norm_pow, div_pow, hc]`. Establish `hpi` using `Real.pi_pos`.

Rewrite using `[hy, hd]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[cos, hnum, hn, ← ha_def]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[fs, hn, ← hD_def]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem cos_fs_moebius (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (x : ℂ)
    (hx : 1 + G 1 0 / G 0 0 * x ≠ 0) :
    GlobalTheory.FibCos.cos G x = 1 / (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ∧
    GlobalTheory.FibCos.fs G x = ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) / (1 + G 1 0 / G 0 0 * x) ^ 2‖ ^ 2 *
      (1 / (Real.pi * (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ^ 2)) := by
  have h00 : (0 : ℂ) < G 0 0 := hG.diag_pos
  have hdet : (0 : ℂ) < G.det := hG.det_pos
  obtain ⟨ha, ha'⟩ := Complex.pos_iff.mp h00
  obtain ⟨hD, -⟩ := Complex.pos_iff.mp hdet
  have h01 : G 0 1 = (starRingEnd ℂ) (G 1 0) := (hG.isHermitian.apply 0 1).symm
  set a : ℝ := (G 0 0).re with ha_def
  set D : ℝ := G.det.re with hD_def
  have hGa : G 0 0 = (a : ℂ) := by
    apply Complex.ext
    · simp [ha_def]
    · simp [← ha']
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set u : ℝ := ‖1 + G 1 0 / G 0 0 * x‖ ^ 2 with hu_def
  set s : ℝ := ‖x‖ ^ 2 with hs_def
  have hu : 0 < u := by positivity
  have hs : 0 ≤ s := by positivity
  have hnum : ‖G 0 0 + x * G 1 0‖ ^ 2 = a ^ 2 * u := by
    have : G 0 0 + x * G 1 0 = (a : ℂ) * (1 + G 1 0 / G 0 0 * x) := by
      rw [hGa]; field_simp
    rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hDe : D = a * (G 1 1).re - ((G 1 0).re ^ 2 + (G 1 0).im ^ 2) := by
    rw [hD_def, Matrix.det_fin_two, h01, hGa]
    simp
    ring
  have hn : nrm G x = a * u + D / a * s := by
    have h1 : a * nrm G x = a ^ 2 * u + D * s := by
      rw [← hnum, hDe, hs_def, nrm, h01, hGa]
      simp only [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    field_simp
    linarith
  have hc : ‖(Real.sqrt D / a : ℂ)‖ ^ 2 = D / a ^ 2 := by
    rw [norm_div, div_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs, Real.sq_sqrt hD.le]
  have hy : ‖(Real.sqrt D / a : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2 = D / a ^ 2 * s / u := by
    rw [norm_div, norm_mul, div_pow, mul_pow, hc]
  have hd : ‖(Real.sqrt D / a : ℂ) / (1 + G 1 0 / G 0 0 * x) ^ 2‖ ^ 2 = D / a ^ 2 / u ^ 2 := by
    rw [norm_div, norm_pow, div_pow, hc]
  have hpi := Real.pi_pos
  rw [hy, hd]
  constructor
  · rw [cos, hnum, hn, ← ha_def]
    field_simp
  · rw [fs, hn, ← hD_def]
    field_simp

end GlobalTheory.FibCos
