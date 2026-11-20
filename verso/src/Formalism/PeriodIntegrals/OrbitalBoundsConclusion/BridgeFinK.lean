import Mathlib
import Formalism.PeriodIntegrals.AdBridgeSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.VecVMulVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocFrom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocInj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocLift

/- English proof (translation)
The claim follows from `PI.FinKW.finK_of PI.FinKW.LocTo.mem_local_lattice_iff (PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective) PI.FinKW.local_vector_lift`.
-/
theorem adelic_compact_finite_places : PI.AdBridgeSteps.FinK :=
  PI.FinKW.finK_of PI.FinKW.LocTo.mem_local_lattice_iff (PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective)
    PI.FinKW.local_vector_lift
