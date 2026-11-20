import Formalism.PeriodIntegrals.StdCharTR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardCharacterTrace.SumEmbeddingEqTrace

/- English proof (translation)
The claim follows from `PI.StdCharTRWork.stdCharTR_main`.
-/
theorem stdCharTR : PI.StdCharTR.Target :=
  PI.StdCharTRWork.stdCharTR_main
