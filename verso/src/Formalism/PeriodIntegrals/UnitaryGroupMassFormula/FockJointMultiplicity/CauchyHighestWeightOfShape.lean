import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurCauchy
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.BlockDegreeAntitone

namespace PI.FJMB

/- English proof (translation)
Use `cauchyHW_of ?_ hS hD hF` and prove the remaining obligations. Introduce `σ m n ι hι α P hP hrow hdeg`. Conclude with `PI.FJMF.block_degree_antitone σ m n ι hι α P hP hrow hdeg`.
-/
theorem cauchy_highest_weight_of_shape (hS : HypShape) (hD : HypDiag) (hF : HypFree) : PI.FJM.CauchyHW := by
  refine cauchyHW_of ?_ hS hD hF
  intro σ m n ι hι α P hP hrow hdeg
  exact PI.FJMF.block_degree_antitone σ m n ι hι α P hP hrow hdeg

end PI.FJMB
