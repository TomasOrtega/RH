import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductGradedCommRingAxiomsHold
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | (exact @GlobalTheory.EtC.a6ring_holds) | (exact GlobalTheory.EtC.a6ring_holds) | (intros; apply GlobalTheory.EtC.a6ring_holds <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold : GlobalTheory.EtC.DivisorRingCompatibility := by
  first | (exact @GlobalTheory.EtC.a6ring_holds) | (exact GlobalTheory.EtC.a6ring_holds) | (intros; apply GlobalTheory.EtC.a6ring_holds  <;> assumption)
