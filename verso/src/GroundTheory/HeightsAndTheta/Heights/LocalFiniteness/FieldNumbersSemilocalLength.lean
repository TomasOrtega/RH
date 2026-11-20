import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalLengthSum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleMinimal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreRelDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLength
set_option maxSynthPendingDepth 1

/- English proof (translation)
The claim follows from `@GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLength.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLengthSum GroundTheory.Heights₂.Heights.FieldNumbers.FibreRelDim.proof GroundTheory.Heights₂.Heights.FieldNumbers.DivCycleMinimal.proof GroundTheory …`.
-/
theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLength.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLengthSum GroundTheory.Heights₂.Heights.FieldNumbers.FibreRelDim.proof GroundTheory.Heights₂.Heights.FieldNumbers.DivCycleMinimal.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength
