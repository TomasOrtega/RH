import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylForU
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ModelIso
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PolyCoef
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDense
import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem nablaDim_closed : PI.NablaDim := fun n nu h => Formalism.L2.G.Model.weyl_dualWeyl ℂ n nu h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem modelIso_closed : PI.ModelIso := modelIso_of polynomial_coefficients unitaryGroupDense_holds highest_weight_irreducible

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weylForU_closed : PI.WeylForU := weylForU_of modelIso_closed nablaDim_closed
