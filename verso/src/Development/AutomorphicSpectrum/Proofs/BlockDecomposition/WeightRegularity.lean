import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.StepsD
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.TrDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula

noncomputable section

open Ad3.LR

namespace GlobalTheory.CompanionTheory.WeightRegular

/- English proof (translation)
Establish `hdi : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹`. Rewrite using `[Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Establish `hn : ¬ 0 < ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det`. Rewrite using `[hdi]`. Conclude with `not_lt.mpr (inv_nonpos.mpr hd.le)`.

Unfold `w0 Wm`. Rewrite using `[if_neg hn]`. Simplify using the standard rewrite rules.
-/
theorem weight_eq_zero_neg_det (k : ℕ) (h : M22) (hd : (Matrix.of h).det < 0) : w0 k h = 0 := by
  have hdi : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hn : ¬ 0 < ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [hdi]
    exact not_lt.mpr (inv_nonpos.mpr hd.le)
  unfold w0 Wm
  rw [if_neg hn]
  simp

/- English proof (translation)
The claim follows from `(contDiff_apply_apply ℝ ℝ i j)`.
-/
theorem contDiff_entry (i j : Fin 2) : ContDiff ℝ ⊤ (fun h : M22 => h i j) :=
  (contDiff_apply_apply ℝ ℝ i j)

/- English proof (translation)
The claim follows from `Complex.ofRealCLM.contDiff.comp (contDiff_entry i j)`.
-/
theorem contDiff_entryC (i j : Fin 2) : ContDiff ℝ ⊤ (fun h : M22 => ((h i j : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_entry i j)

/- English proof (translation)
Establish `: (fun h : M22 => (Matrix.of h).det) = fun h : M22 => h 0 0 * h 1 1 - h 0 1 * h 1 0`. Use function extensionality and compare the values at `h`. Simplify using `[Matrix.det_fin_two]`. Rewrite using `[this]`. Apply the tactic sequence `exact ((contDiff_entry 0 0).mul (contDiff_entry 1 1)).sub ((contDiff_entry 0 1).mul (contDiff_entry 1 0))`.
-/
theorem contDiff_det : ContDiff ℝ ⊤ (fun h : M22 => (Matrix.of h).det) := by
  have : (fun h : M22 => (Matrix.of h).det) = fun h : M22 => h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    funext h
    simp [Matrix.det_fin_two]
  rw [this]
  exact ((contDiff_entry 0 0).mul (contDiff_entry 1 1)).sub
    ((contDiff_entry 0 1).mul (contDiff_entry 1 0))

/- English proof (translation)
Establish `hF : ContDiffOn ℝ ⊤ (fun h : M22 => (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) * ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) * Complex.exp (2 * Real.pi * Complex.I * (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I)))) {h : M22 | 0 …`. Introduce `h hh`. Apply `ContDiffAt.contDiffWithinAt` to reduce the goal to its premises. Establish `hα` using `GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hh`. Establish `cα : ContDiffAt ℝ ⊤ (fun h : M22 => (h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) h` using `((contDiff_entryC 0 0).add ((contDiff_entryC 1 0).mul contDiff_const)).contDiffAt`.

Establish `cβ : ContDiffAt ℝ ⊤ (fun h : M22 => (h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) h` using `((contDiff_entryC 0 1).add ((contDiff_entryC 1 1).mul contDiff_const)).contDiffAt`. Establish `cd : ContDiffAt ℝ ⊤ (fun h : M22 => (((Matrix.of h).det : ℝ) : ℂ)) h` using `(Complex.ofRealCLM.contDiff.comp contDiff_det).contDiffAt`. Establish `e : -(2 * (k : ℤ) - 1) = -(((2 * k - 1 : ℕ)) : ℤ)`. Establish `: 1 ≤ 2 * k` using `by omega`. Move the coercions through the operations in `[Nat.cast_sub this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `cz : ContDiffAt ℝ ⊤ (fun h : M22 => ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1))) h`. Simplify using `only [e, zpow_neg, zpow_natCast]`. Conclude with `(cα.pow _).inv (pow_ne_zero _ hα)`. Establish `cq : ContDiffAt ℝ ⊤ (fun h : M22 => ((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I)) h`.

Simplify using `only [div_eq_mul_inv]`. Conclude with `cβ.mul (cα.inv hα)`. Establish `ce : ContDiffAt ℝ ⊤ (fun h : M22 => Complex.exp (2 * Real.pi * Complex.I * (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I)))) h` using `(contDiffAt_const.mul cq).cexp`. Conclude with `((cd.pow _).mul cz).mul ce`. Conclude with `hF.congr fun h hh => GlobalTheory.CompanionTheory.WeightClosed.main k hk h hh`.
-/
theorem contDiffOn_weight_pos_det (k : ℕ) (hk : 3 ≤ k) :
    ContDiffOn ℝ ⊤ (w0 k) {h : M22 | 0 < (Matrix.of h).det} := by
  have hF : ContDiffOn ℝ ⊤ (fun h : M22 =>
      (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) *
        ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) *
        Complex.exp (2 * Real.pi * Complex.I *
          (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I))))
      {h : M22 | 0 < (Matrix.of h).det} := by
    intro h hh
    apply ContDiffAt.contDiffWithinAt
    have hα := GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hh
    have cα : ContDiffAt ℝ ⊤ (fun h : M22 => (h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) h :=
      ((contDiff_entryC 0 0).add ((contDiff_entryC 1 0).mul contDiff_const)).contDiffAt
    have cβ : ContDiffAt ℝ ⊤ (fun h : M22 => (h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) h :=
      ((contDiff_entryC 0 1).add ((contDiff_entryC 1 1).mul contDiff_const)).contDiffAt
    have cd : ContDiffAt ℝ ⊤ (fun h : M22 => (((Matrix.of h).det : ℝ) : ℂ)) h :=
      (Complex.ofRealCLM.contDiff.comp contDiff_det).contDiffAt
    have e : -(2 * (k : ℤ) - 1) = -(((2 * k - 1 : ℕ)) : ℤ) := by
      have : 1 ≤ 2 * k := by omega
      push_cast [Nat.cast_sub this]
      ring
    have cz : ContDiffAt ℝ ⊤ (fun h : M22 =>
        ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1))) h := by
      simp only [e, zpow_neg, zpow_natCast]
      exact (cα.pow _).inv (pow_ne_zero _ hα)
    have cq : ContDiffAt ℝ ⊤ (fun h : M22 =>
        ((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I)) h := by
      simp only [div_eq_mul_inv]
      exact cβ.mul (cα.inv hα)
    have ce : ContDiffAt ℝ ⊤ (fun h : M22 => Complex.exp (2 * Real.pi * Complex.I *
        (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I)))) h :=
      (contDiffAt_const.mul cq).cexp
    exact ((cd.pow _).mul cz).mul ce
  exact hF.congr fun h hh => GlobalTheory.CompanionTheory.WeightClosed.main k hk h hh

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h hd => weight_eq_zero_neg_det k h hd, contDiffOn_weight_pos_det k hk⟩`.
-/
theorem main_analytic (k : ℕ) (hk : 3 ≤ k) :
    (∀ h : M22, (Matrix.of h).det < 0 → w0 k h = 0) ∧
      ContDiffOn ℝ ⊤ (w0 k) {h : M22 | 0 < (Matrix.of h).det} :=
  ⟨fun h hd => weight_eq_zero_neg_det k h hd, contDiffOn_weight_pos_det k hk⟩

/- English proof (translation)
Introduce `k hk` and use `⟨(main_analytic k hk).1, (main_analytic k hk).2.of_le le_top⟩`.
-/
theorem main : Ad3.LR.DTr.WeightVanishesNegDetSmoothPosDet := fun k hk =>
  ⟨(main_analytic k hk).1, (main_analytic k hk).2.of_le le_top⟩

end GlobalTheory.CompanionTheory.WeightRegular
