import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylForU
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ModelIso
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PolyCoef
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDense
import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim

/- English proof (translation)
Introduce `n nu h` and use `Formalism.L2.G.Model.weyl_dualWeyl ℂ n nu h`.
-/
theorem nablaDim_closed : PI.NablaDim := fun n nu h => Formalism.L2.G.Model.weyl_dualWeyl ℂ n nu h

/- English proof (translation)
The claim follows from `modelIso_of polynomial_coefficients unitaryGroupDense_holds highest_weight_irreducible`.
-/
theorem modelIso_closed : PI.ModelIso := modelIso_of polynomial_coefficients unitaryGroupDense_holds highest_weight_irreducible

/- English proof (translation)
The claim follows from `weylForU_of modelIso_closed nablaDim_closed`.
-/
theorem weylForU_closed : PI.WeylForU := weylForU_of modelIso_closed nablaDim_closed
