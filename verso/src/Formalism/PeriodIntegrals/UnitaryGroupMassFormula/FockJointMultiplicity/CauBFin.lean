import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurCauchy
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LeadTDerCols

namespace PI.FJMX

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem minorProductDiagonal : PI.FJMB.HypShape := fun _ _ ι hι α hα =>
  ⟨shapeProd_hwb ι hι _, shapeProd_diag ι hι α hα⟩

end PI.FJMX
