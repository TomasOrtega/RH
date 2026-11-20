import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral
import Mathlib
import Formalism.ResultantValuation.ResultantAdjugateProofs.Adjugate
import Formalism.ResultantValuation.ResultantAdjugateProofs.Mobius
import Formalism.ResultantValuation.ResultantAdjugateProofs.Window
import Formalism.ResultantValuation.ResultantAdjugateProofs.Koszul
import Formalism.ResultantValuation.ResultantAdjugateProofs.Parabolic
import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace
import Formalism.ResultantValuation.PrimePairDyadicDisjointAlt
import Formalism.CyclotomicNorms.IrreducibilityOfGoodTuple
import Formalism.CyclotomicNorms.SubstitutionAdaptive
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AuxiliaryNormPrimes
import Formalism.CyclotomicNorms.NonsquarefreeBounds.ResModule

open Finset Polynomial

namespace Formalism.IrreducibleCountingLemmas.TW

/- English proof (translation)
The claim follows from `Formalism.CyclotomicNorms.substitutionAdaptive`.
-/
theorem substitution_SUB : LemmaSUB := Formalism.CyclotomicNorms.substitutionAdaptive
/- English proof (translation)
The claim follows from `Formalism.CyclotomicNorms.lowPowerSeries`.
-/
theorem low_power_series_LOW : LemmaLOW := Formalism.CyclotomicNorms.lowPowerSeries

end Formalism.IrreducibleCountingLemmas.TW
