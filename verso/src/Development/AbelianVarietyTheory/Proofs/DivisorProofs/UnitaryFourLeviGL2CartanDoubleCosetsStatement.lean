import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2CartanDoubleCosets
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SatakeWeyl.Four.cartanFour` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryFourLeviGL2CartanDoubleCosets.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.unitaryFourLeviGL2_cartan_doubleCosets : GlobalTheory.SatakeWeyl.CartanFour := by
  first | exact @GlobalTheory.SatakeWeyl.Four.cartanFour | exact GlobalTheory.SatakeWeyl.Four.cartanFour | (intros; apply GlobalTheory.SatakeWeyl.Four.cartanFour <;> assumption)
