import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLevelPrimeLawAllTuples
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSeesawLevelPrimeLawAllTuples.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.seesaw_levelPrime_law_all_tuples : ∀ D : D7, GlobalTheory.SeeSaw.TOfShape D := by
  first | exact @GlobalTheory.LevPrimeAll.lawLevelPrime_all | exact GlobalTheory.LevPrimeAll.lawLevelPrime_all | (intros; apply GlobalTheory.LevPrimeAll.lawLevelPrime_all <;> assumption)
