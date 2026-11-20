import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianBasisVectorTraceFreeSkewCond
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsIdent
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSkewHermitianBasisVectorTraceFreeSkewCond.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.skewHermitianBasisVector_traceFreeSkewCond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, SkewCond d (boxVec d z k) := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec | exact GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec <;> assumption)
