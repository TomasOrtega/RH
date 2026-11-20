import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentMemSpecialUnitaryLieDiagonal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsOrth
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorusTangentMemSpecialUnitaryLieDiagonal.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.torusTangent_mem_specialUnitaryLie_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∀ θ : X.Ψ → Fin (r - 1) → ℝ, torusDer x θ ∈ realLie X.Ψ X.Gm ∧ ∀ τ a b, inFrame x (torusDer x θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0 := by
  first | exact @GlobalTheory.TorusFrame.torusDer_mem_realLie_and_inFrame | exact GlobalTheory.TorusFrame.torusDer_mem_realLie_and_inFrame | (intros; apply GlobalTheory.TorusFrame.torusDer_mem_realLie_and_inFrame <;> assumption)
