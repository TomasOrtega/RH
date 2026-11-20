import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentRadicalSplittingOfLeviPart
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | exact GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | (intros; apply GlobalTheory.SatakeWeyl.unipSplit_of_leviPart <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart : GlobalTheory.SatakeWeyl.LeviPart → GlobalTheory.SatakeWeyl.UnipSplit := by
  first | exact @GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | exact GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | (intros; apply GlobalTheory.SatakeWeyl.unipSplit_of_leviPart <;> assumption)
