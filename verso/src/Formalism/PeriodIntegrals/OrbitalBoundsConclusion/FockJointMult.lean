import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.FockJointMultOfCauchy
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyFin

/- English proof (translation)
The claim follows from `PI.FJM.fockJointMult_of_cauchy PI.FJM.cauchy_highest_weight`.
-/
theorem fock_joint_multiplicity : PI.FockDegreeTwoParts.JointMult := PI.FJM.fockJointMult_of_cauchy PI.FJM.cauchy_highest_weight
