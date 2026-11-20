import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetUnitaryChartSectionConjugatedMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SUChartSection.det_secM_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDetUnitaryChartSectionConjugatedMatrix.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ τ : X.Ψ, (secM X x w τ).det = 1 := by
  first | exact @GlobalTheory.SUChartSection.det_secM_eq_one | exact GlobalTheory.SUChartSection.det_secM_eq_one | (intros; apply GlobalTheory.SUChartSection.det_secM_eq_one <;> assumption)
