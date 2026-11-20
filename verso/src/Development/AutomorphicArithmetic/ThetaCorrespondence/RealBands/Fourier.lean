import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

open scoped FourierTransform in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Lit.Cusp.fourier_zero :
    ∀ u : ℝ → ℂ, Continuous u → Integrable u →
      (∀ s : ℝ, ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * u t = 0) → ∀ t, u t = 0 := by
  intro u hc hi hz t
  have hF : 𝓕 u = 0 := by
    ext w
    rw [Real.fourier_real_eq_integral_exp_smul, Pi.zero_apply, ← hz (2 * Real.pi * w)]
    congr 1
    ext v
    rw [smul_eq_mul]
    congr 1
    congr 1
    push_cast
    ring
  have hinv := hc.fourierInv_fourier_eq hi (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  simp [Real.fourierInv_eq]
