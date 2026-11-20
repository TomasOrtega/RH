import Mathlib
import Formalism.PeriodIntegrals.GeometricProductPowers.GaussianProductPowerBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GeometricProductBound.OneSubSumLeProd

/- English proof (translation)
The claim follows from `GeoProdPow.main`.
-/
theorem geometric_product_power : ConditionalKappaBounds.G2.GaussianProductPowerBound := GeoProdPow.main
