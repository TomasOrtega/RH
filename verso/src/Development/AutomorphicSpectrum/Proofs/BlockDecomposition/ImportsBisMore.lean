import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness

noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.KerZeroPf

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

/- English proof (translation)
Introduce `n _ _ μ _ E κ hκ hr hf y hy`. Use `GlobalTheory.CompanionTheory.KerUniq.main n μ E κ (GLs n) GlobalTheory.CompanionTheory.KerUniq.isOpen_GLs subset_rfl ?_ hκ hr ?_ y hy` and prove the remaining obligations. Introduce `y hy k₂`. Establish `hk : (k₂.1).det ≠ 0`. Establish `h : k₂.1 * star k₂.1 = 1` using `(Matrix.mem_unitaryGroup_iff).1 k₂.2`.

Introduce `h0`. Establish `h1` using `congrArg Matrix.det h`. Rewrite `h1` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one h1`. Use `show (y * k₂.1).det ≠ 0`.

Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero hy hk`. Introduce `f hfE hc _`. Establish `h` using `hf f hfE hc`. Simplify `h` using `[act]`.
-/
theorem main : PositivityTheory.RgBcC.KerZero := by
  intro n _ _ μ _ E κ hκ hr hf y hy
  refine GlobalTheory.CompanionTheory.KerUniq.main n μ E κ (GLs n) GlobalTheory.CompanionTheory.KerUniq.isOpen_GLs subset_rfl ?_ hκ hr ?_ y hy
  · intro y hy k₂
    have hk : (k₂.1).det ≠ 0 := by
      have h : k₂.1 * star k₂.1 = 1 := (Matrix.mem_unitaryGroup_iff).1 k₂.2
      intro h0
      have h1 := congrArg Matrix.det h
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
      exact zero_ne_one h1
    show (y * k₂.1).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hy hk
  · intro f hfE hc _
    have h := hf f hfE hc
    simpa [act] using h

end GlobalTheory.CompanionTheory.KerZeroPf
