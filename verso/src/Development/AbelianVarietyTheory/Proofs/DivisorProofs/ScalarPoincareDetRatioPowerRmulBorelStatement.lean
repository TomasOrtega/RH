import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerRmulBorel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ScalarPoin.qS_rmul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FScalarPoincareDetRatioPowerRmulBorel.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.scalarPoincareDetRatioPower_rmul_borel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x b : Frame X.Ψ r), b ∈ Bor X.Ψ r → qS X x0 k (rmul x b) = bchar (laS X k) b * qS X x0 k x := by
  first | exact @GlobalTheory.ScalarPoin.qS_rmul | exact GlobalTheory.ScalarPoin.qS_rmul | (intros; apply GlobalTheory.ScalarPoin.qS_rmul <;> assumption)
