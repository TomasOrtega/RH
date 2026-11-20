import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitZeroClosedness.SplitZeroGBd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitZeroClosedness.IsClosedSimeqZero

/- English proof (translation)
The claim follows from `PI.SZGW.splitZeroG_of PI.SZGW.zpSimeq_holds PI.SZGW.zpInt_holds PI.SZGW.zcFacts_holds`.
-/
theorem split_zero_g : PI.SplitZeroG.SplitZeroG :=
  PI.SZGW.splitZeroG_of PI.SZGW.zpSimeq_holds PI.SZGW.zpInt_holds PI.SZGW.zcFacts_holds
