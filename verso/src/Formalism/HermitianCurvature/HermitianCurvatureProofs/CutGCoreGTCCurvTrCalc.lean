import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

/- English proof (translation)
Use function extensionality and compare the values at `w`. Establish `h : (w * star w : ℂ) = (Complex.normSq w : ℂ)` using `Complex.mul_conj w`. Rewrite using `[h]`. Simplify using `only [modA, div_eq_mul_inv]`.
-/
theorem modA_eq_fun (P : M.Par) (ρ : M.Ty P) :
    modA P ρ = fun w => (M.aC P ρ : ℂ) * star w * (w * star w - (P.TT : ℂ))⁻¹ := by
  funext w
  have h : (w * star w : ℂ) = (Complex.normSq w : ℂ) := Complex.mul_conj w
  rw [h]
  simp only [modA, div_eq_mul_inv]

/- English proof (translation)
Establish `hns : (ζ * star ζ : ℂ) = (Complex.normSq ζ : ℂ)` using `Complex.mul_conj ζ`. Establish `hlt : P.TT < Complex.normSq ζ` using `hζ`. Establish `hN0 : ζ * star ζ - (P.TT : ℂ) ≠ 0`. Rewrite using `[hns, ← Complex.ofReal_sub]`. Conclude with `Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hlt.ne')`.

Establish `hS` using `(hasFDerivAt_id (𝕜 := ℝ) ζ).star`. Establish `hN` using `((hasFDerivAt_id (𝕜 := ℝ) ζ).mul hS).sub_const (P.TT : ℂ)`. Establish `hI` using `((hasDerivAt_inv hN0).hasFDerivAt.restrictScalars ℝ).comp ζ hN`. Establish `hF` using `((hasFDerivAt_const (𝕜 := ℝ) (M.aC P ρ : ℂ) ζ).mul hS).mul hI`. Establish `hF' : HasFDerivAt (fun w : ℂ => (M.aC P ρ : ℂ) * star w * (w * star w - (P.TT : ℂ))⁻¹) _ ζ` using `hF`.

Rewrite using `[modA_eq_fun]`. Simplify using `only [NF.dZb]`. Rewrite using `[hF'.fderiv]`. Rewrite using `[← hns]`. Simplify using `[Complex.star_def]`.

Clear the denominators using the available nonvanishing facts. Put the polynomial expressions in normal form. Simplify using `only [Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dZb_modA (P : M.Par) (ρ : M.Ty P) {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    NF.dZb (modA P ρ) ζ = -(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2 := by
  have hns : (ζ * star ζ : ℂ) = (Complex.normSq ζ : ℂ) := Complex.mul_conj ζ
  have hlt : P.TT < Complex.normSq ζ := hζ
  have hN0 : ζ * star ζ - (P.TT : ℂ) ≠ 0 := by
    rw [hns, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hlt.ne')
  have hS := (hasFDerivAt_id (𝕜 := ℝ) ζ).star
  have hN := ((hasFDerivAt_id (𝕜 := ℝ) ζ).mul hS).sub_const (P.TT : ℂ)
  have hI := ((hasDerivAt_inv hN0).hasFDerivAt.restrictScalars ℝ).comp ζ hN
  have hF := ((hasFDerivAt_const (𝕜 := ℝ) (M.aC P ρ : ℂ) ζ).mul hS).mul hI
  have hF' : HasFDerivAt (fun w : ℂ => (M.aC P ρ : ℂ) * star w * (w * star w - (P.TT : ℂ))⁻¹) _ ζ := hF
  rw [modA_eq_fun]
  simp only [NF.dZb]
  rw [hF'.fderiv]
  rw [← hns]
  simp [Complex.star_def]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/- English proof (translation)
Rewrite using `[dZb_modA P ρ hζ]`. Establish `h : (-(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2) = ((-(M.aC P ρ * P.TT) / (Complex.normSq ζ - P.TT) ^ 2 : ℝ) : ℂ)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, Complex.ofReal_re]`.
-/
theorem re_dZb_modA (P : M.Par) (ρ : M.Ty P) {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    (NF.dZb (modA P ρ) ζ).re = -(M.aC P ρ * P.TT) / (Complex.normSq ζ - P.TT) ^ 2 := by
  rw [dZb_modA P ρ hζ]
  have h : (-(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2) =
      ((-(M.aC P ρ * P.TT) / (Complex.normSq ζ - P.TT) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.ofReal_re]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
