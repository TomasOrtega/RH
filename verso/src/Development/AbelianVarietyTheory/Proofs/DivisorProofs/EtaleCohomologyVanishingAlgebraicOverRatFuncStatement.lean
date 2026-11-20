import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyVanishingAlgebraicOverRatFunc
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc : GlobalTheory.EtC.C1 := by
  first | (exact @GlobalTheory.EtC.gaugeSplitting_holds) | (exact GlobalTheory.EtC.gaugeSplitting_holds) | (intros; apply GlobalTheory.EtC.gaugeSplitting_holds  <;> assumption)
