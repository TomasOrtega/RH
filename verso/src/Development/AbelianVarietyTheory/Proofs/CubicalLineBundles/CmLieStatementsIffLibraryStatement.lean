import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieStatementsIffLibrary
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LamF.lambdaBundle_conditions_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCubicalLineBundles%2FCmLieStatementsIffLibrary.lean&line=157#L157)
-/
theorem _root_.GlobalTheory.T.cmLieStatements_iff_library : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (x : ℝ), GlobalTheory.LamF.LamDegSt H x ↔ Formalism.L2.Pj.abelian₂.LamDegSt H x) ∧ (GlobalTheory.LamF.LamIndSt ↔ Formalism.L2.Pj.abelian₂.LamIndSt) ∧ (GlobalTheory.LamF.LamLenSt ↔ Formalism.L2.Pj.abelian₂.LamLenSt) := by
  first | exact @GlobalTheory.LamF.lambdaBundle_conditions_iff | exact GlobalTheory.LamF.lambdaBundle_conditions_iff | (intros; apply GlobalTheory.LamF.lambdaBundle_conditions_iff <;> assumption)
