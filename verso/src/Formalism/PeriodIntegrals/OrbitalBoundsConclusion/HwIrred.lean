import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionB

/- English proof (translation)
The claim follows from `PI.WHw.hwIrred_of PI.WHw.stable_subspace_closed PI.WHw.fixed_vectors_killed PI.WHw.highest_weight_in_closure PI.WHw.closure_eq_nabla`.
-/
theorem highest_weight_irreducible : PI.HwIrred :=
  PI.WHw.hwIrred_of PI.WHw.stable_subspace_closed PI.WHw.fixed_vectors_killed PI.WHw.highest_weight_in_closure
    PI.WHw.closure_eq_nabla
