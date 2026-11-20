import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ Ψ y` using `((hΨ y hy).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)`. Establish `h : HasFDerivAt (fun z => (Ψ z : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ Ψ y)) y` using `Complex.ofRealCLM.hasFDerivAt.comp y hd.hasFDerivAt`. Simplify using `only [Rd, Rr, h.fderiv]`. Both sides reduce to the same expression.
-/
theorem Rd_ofReal_eq {n : ℕ} {Ψ : Mat n → ℝ} (hΨ : ContDiffOn ℝ ∞ Ψ (GLs n)) (X : Mat n)
    {y : Mat n} (hy : y ∈ GLs n) :
    Rd X (fun z => (Ψ z : ℂ)) y = ((Rr X Ψ y : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ Ψ y :=
    ((hΨ y hy).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
  have h : HasFDerivAt (fun z => (Ψ z : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ Ψ y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hd.hasFDerivAt
  simp only [Rd, Rr, h.fderiv]
  rfl

/- English proof (translation)
Introduce `hR n _ _ μ _ Ψ hΨ hc X`. Establish `hf : ContDiffOn ℝ ∞ (fun z => (Ψ z : ℂ)) (GLs n)` using `Complex.ofRealCLM.contDiff.comp_contDiffOn hΨ`. Establish `hcf : Cpt (fun z => (Ψ z : ℂ))`. Take `⟨R, hR'⟩` from `hc`. Conclude with `⟨R, fun y hy h => by simp [hR' y hy h]⟩`.

Establish `h0` using `(hR n).2.2 μ ℂ (fun z => (Ψ z : ℂ)) hf hcf X`. Establish `h1 : (fun y : G n => Rd X (fun z => (Ψ z : ℂ)) y.val) = fun y : G n => ((Rr X Ψ y.val : ℝ) : ℂ)`. Use function extensionality and compare the values at `fun y => Rd_ofReal_eq hΨ X (val_mem_GLs y)`. Rewrite `h0` using `[h1, integral_complex_ofReal]`. Conclude with `Complex.ofReal_eq_zero.1 h0`.
-/
theorem integral_Rr_eq_zero : RCalc → ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (Ψ : Mat n → ℝ), ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0 := by
  intro hR n _ _ μ _ Ψ hΨ hc X
  have hf : ContDiffOn ℝ ∞ (fun z => (Ψ z : ℂ)) (GLs n) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hΨ
  have hcf : Cpt (fun z => (Ψ z : ℂ)) := by
    obtain ⟨R, hR'⟩ := hc
    exact ⟨R, fun y hy h => by simp [hR' y hy h]⟩
  have h0 := (hR n).2.2 μ ℂ (fun z => (Ψ z : ℂ)) hf hcf X
  have h1 : (fun y : G n => Rd X (fun z => (Ψ z : ℂ)) y.val) =
      fun y : G n => ((Rr X Ψ y.val : ℝ) : ℂ) :=
    funext fun y => Rd_ofReal_eq hΨ X (val_mem_GLs y)
  rw [h1, integral_complex_ofReal] at h0
  exact Complex.ofReal_eq_zero.1 h0

end GlobalTheory.CompanionTheory.WaveSpd
