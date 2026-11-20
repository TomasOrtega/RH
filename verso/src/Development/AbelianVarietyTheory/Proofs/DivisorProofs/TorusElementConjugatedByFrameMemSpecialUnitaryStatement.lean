import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementConjugatedByFrameMemSpecialUnitary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsOrth
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorusFrame.torusGL_mem_realSU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorusElementConjugatedByFrameMemSpecialUnitary.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.torusElementConjugatedByFrame_mem_specialUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ), torusGL hx θ ∈ realSU X.Ψ X.Gm := by
  first | exact @GlobalTheory.TorusFrame.torusGL_mem_realSU | exact GlobalTheory.TorusFrame.torusGL_mem_realSU | (intros; apply GlobalTheory.TorusFrame.torusGL_mem_realSU <;> assumption)
