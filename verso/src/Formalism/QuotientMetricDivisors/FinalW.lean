import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.CommutingTwist
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ClassSumDualGeOfFamily
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.PlaceSumSquares
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.KappaNormalise
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DescendedNorm
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.YoungDiagramHook
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.YoungDiagramTopExact
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TwistedLatticeNaturality
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondComplementParameterBounds
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.WeightedPlaceLogSum

namespace Formalism.DivisionValues

/- English proof (translation)
The claim follows from `bounds_fourth_general`.
-/
theorem boundsIVal : BoundsIVal := bounds_fourth_general

/- English proof (translation)
The claim follows from `lattice_gluing`.
-/
theorem latticeGlue : LatticeGlue := lattice_gluing

/- English proof (translation)
The claim follows from `frobenius_norm_rational`.
-/
theorem fnormRat : FnormRat := frobenius_norm_rational
/- English proof (translation)
The claim follows from `quotient_metric_representation`.
-/
theorem quotMetricRep : QuotMetricRep := quotient_metric_representation
/- English proof (translation)
The claim follows from `chain_spectrum`.
-/
theorem chainSpec : ChainSpec := chain_spectrum
/- English proof (translation)
The claim follows from `composition_norm`.
-/
theorem compNorm : CompNorm := composition_norm
/- English proof (translation)
The claim follows from `height_constant_first`.
-/
theorem height_constant_bound : HeightBoundConstant := height_constant_first

/- English proof (translation)
The claim follows from `young_diagram_hook`.
-/
theorem rowsHook : RowsHook := young_diagram_hook

/- English proof (translation)
The claim follows from `young_diagram_step_origin`.
-/
theorem rowsStepEOrigin : RowsStepEOrigin := young_diagram_step_origin

/- English proof (translation)
The claim follows from `shift_slope_mu`.
-/
theorem shiftMu : ShiftMu := shift_slope_mu
/- English proof (translation)
The claim follows from `shift_existence`.
-/
theorem shiftEx : ShiftEx := shift_existence
/- English proof (translation)
The claim follows from `lattice_weight_sum_prime`.
-/
theorem lwSumPrime : LwSumPrime := lattice_weight_sum_prime
/- English proof (translation)
The claim follows from `divisor_into_dual_shift`.
-/
theorem divIntoDualShift : DivIntoDualShift := divisor_into_dual_shift

/- English proof (translation)
The claim follows from `prime_log_sum_bound`.
-/
theorem primeLogSum : PrimeLogSum := prime_log_sum_bound

end Formalism.DivisionValues
