import Formalism.PeriodIntegrals.SqPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairGluing.SqPairGlueMain

/- English proof (translation)
The claim follows from `PI.SqPairW.sqPairGlue_main`.
-/
theorem square_pair_glue : PI.SqPair.PLocalAll → Formalism.L2.PairingIndexBounds.Eq.SqG.SplitPairGen :=
  PI.SqPairW.sqPairGlue_main
