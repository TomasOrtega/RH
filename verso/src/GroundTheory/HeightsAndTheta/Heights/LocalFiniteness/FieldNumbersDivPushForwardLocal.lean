import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleMinimal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForwardLocal
set_option maxSynthPendingDepth 1

/- English proof (translation)
The claim follows from `@GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForwardLocal.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DivCycleMinimal.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing Gr …`.
-/
theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForwardLocal.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForwardLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForwardLocal.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DivCycleMinimal.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLength
