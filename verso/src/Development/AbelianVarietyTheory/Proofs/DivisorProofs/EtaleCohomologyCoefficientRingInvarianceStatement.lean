import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvariance
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.EtC.a8`. Consider the case `exact GlobalTheory.EtC.a8`. Consider the case `(intros; apply GlobalTheory.EtC.a8 <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.etaleCohomology_coefficientRing_invariance : GlobalTheory.EtC.A8 := by
  first
  | exact @GlobalTheory.EtC.a8
  | exact GlobalTheory.EtC.a8
  | (intros; apply GlobalTheory.EtC.a8 <;> assumption)
