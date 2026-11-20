import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LevelsOrbits.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FLevelsUsedBalancedValueOrbitSums.lean&line=207#L207)
-/
theorem _root_.GlobalTheory.T.levelsUsed_balancedValue_orbitSums : ThlEq ∧ LevelBound ∧ LemmaFe ∧ FInertReps := by
  first | exact @GlobalTheory.LevelsOrbits.main | exact GlobalTheory.LevelsOrbits.main | (intros; apply GlobalTheory.LevelsOrbits.main <;> assumption)
