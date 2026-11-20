import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeCoeffAdjacentSwapOfLeviReduction
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.SatakeWeyl.Swap.coeffSwap | exact GlobalTheory.SatakeWeyl.Swap.coeffSwap | (intros; apply GlobalTheory.SatakeWeyl.Swap.coeffSwap <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.unitarySatakeCoeff_adjacentSwap_of_leviReduction : GlobalTheory.SatakeWeyl.LeviStep → GlobalTheory.SatakeWeyl.IndexFour → GlobalTheory.SatakeWeyl.CartanFour → GlobalTheory.SatakeWeyl.CoeffSwap := by
  first | exact @GlobalTheory.SatakeWeyl.Swap.coeffSwap | exact GlobalTheory.SatakeWeyl.Swap.coeffSwap | (intros; apply GlobalTheory.SatakeWeyl.Swap.coeffSwap <;> assumption)
