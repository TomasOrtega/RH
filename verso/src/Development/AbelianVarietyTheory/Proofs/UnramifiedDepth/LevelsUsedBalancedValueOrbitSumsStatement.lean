import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.LevelsOrbits.main | exact GlobalTheory.LevelsOrbits.main | (intros; apply GlobalTheory.LevelsOrbits.main <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.levelsUsed_balancedValue_orbitSums : ThlEq ∧ LevelBound ∧ LemmaFe ∧ FInertReps := by
  first | exact @GlobalTheory.LevelsOrbits.main | exact GlobalTheory.LevelsOrbits.main | (intros; apply GlobalTheory.LevelsOrbits.main <;> assumption)
