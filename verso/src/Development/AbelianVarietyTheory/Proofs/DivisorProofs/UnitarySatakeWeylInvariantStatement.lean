import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariant
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.unitarySatake_weylInvariant : Formalism.UG.SatWeyl := by
  first | exact @GlobalTheory.SatakeWeyl.satWeyl | exact GlobalTheory.SatakeWeyl.satWeyl | (intros; apply GlobalTheory.SatakeWeyl.satWeyl <;> assumption)
