import Formalism.SharpRestriction.GrowthBounds.CoeffGaugeSquareLowDegree
import Formalism.SharpRestriction.GrowthBounds.GenIntSPsubst

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem coeffIdentity_selfConj_holds : CoefficientIdentitySelfConjugate := coeffIdentity_selfConj_of_two r1sHLin_holds generic_point_unit_congruence

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem independence_bound_self_conjugate : IndependenceBoundSelfConjugate := independence_bound_self_conj coeffIdentity_selfConj_holds

end Formalism.L2.FormalSeriesBounds
