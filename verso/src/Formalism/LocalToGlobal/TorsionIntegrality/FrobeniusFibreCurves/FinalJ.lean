import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalI
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.FibreIntegerInstanceHolds
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NormXLeOneOfNotInKernel
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Th0TwoAnalyticOf

namespace Formalism.L2.Th1.B

/- English proof (translation)
The claim follows from `Half.half_fibre_exists_holds`.
-/
theorem halfFibreExists : HalfFibreExists := Half.half_fibre_exists_holds
/- English proof (translation)
The claim follows from `Fib.fibre_integer_instance_holds`.
-/
theorem fibreZInstance : FibreZInstance := Fib.fibre_integer_instance_holds
/- English proof (translation)
The claim follows from `Fib.half_shift_series_holds`.
-/
theorem halfShiftSeries : HalfShiftSeries := Fib.half_shift_series_holds
/- English proof (translation)
The claim follows from `Half.fibre_map_holds`.
-/
theorem fibreMap : FibreMap := Half.fibre_map_holds
/- English proof (translation)
The claim follows from `Half.points_integral_at_two_holds`.
-/
theorem pointsIntTwo : PointsIntTwo := Half.points_integral_at_two_holds
/- English proof (translation)
The claim follows from `An2.Th0TwoAnalytic_of halfFibreExists fibreZInstance halfShiftSeries fibreMap`.
-/
theorem th0TwoAnalytic : ThetaZeroTwoAnalytic :=
  An2.Th0TwoAnalytic_of halfFibreExists fibreZInstance halfShiftSeries fibreMap

end Formalism.L2.Th1.B
