import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerDifferentiableOn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FScalarPoincareDetRatioPowerDifferentiableOn.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.scalarPoincareDetRatioPower_differentiableOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ k : ℕ, DifferentiableOn ℂ (qS X x0 k) X.dom := by
  first | exact @GlobalTheory.ScalarPoin.Holo.qS_holomorphicOn | exact GlobalTheory.ScalarPoin.Holo.qS_holomorphicOn | (intros; apply GlobalTheory.ScalarPoin.Holo.qS_holomorphicOn <;> assumption)
