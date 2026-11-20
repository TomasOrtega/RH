import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShearHypothesisOneHolds
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShearHypothesisTwo
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShearCoefficients
import Formalism.NormUnitaryBounds.DetPolynomialWeights.LtSuccOfMemWeightCompositions
import Formalism.NormUnitaryBounds.DetPolynomialWeights.NormUnitary
import Formalism.NormUnitaryBounds.DetPolynomialWeights.NormMul
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
import Formalism.NormUnitaryBounds.DetPolynomialWeights.CoefficientBoundHolds
import Formalism.NormUnitaryBounds.DetPolynomialWeights.GaussianCoefficientFactorialBound

namespace Formalism.NormUnitaryCountingLemmas.Final

/- English proof (translation)
The claim follows from `Formalism.NormUnitaryCountingLemmas.shear_hypothesis_one_holds`.
-/
theorem h1 : Formalism.NormUnitaryCountingLemmas.H1 := Formalism.NormUnitaryCountingLemmas.shear_hypothesis_one_holds
/- English proof (translation)
The claim follows from `Formalism.NormUnitaryCountingLemmas.shear_hypothesis_two`.
-/
theorem h2 : Formalism.NormUnitaryCountingLemmas.H2 := Formalism.NormUnitaryCountingLemmas.shear_hypothesis_two
/- English proof (translation)
The claim follows from `Formalism.NormUnitaryCountingLemmas.shortIndependentVectorsOfDualMinimum`.
-/
theorem gn1 : Formalism.NormUnitaryCountingLemmas.ShortIndependentVectorsOfDualMinimum := Formalism.NormUnitaryCountingLemmas.shortIndependentVectorsOfDualMinimum
/- English proof (translation)
The claim follows from `Formalism.NormUnitaryCountingLemmas.coefficient_bound_holds`.
-/
theorem cb : Formalism.NormUnitaryCountingLemmas.CB := Formalism.NormUnitaryCountingLemmas.coefficient_bound_holds
/- English proof (translation)
The claim follows from `Formalism.NormUnitaryCountingLemmas.gaussian_coefficient_bound_holds`.
-/
theorem n1 : Formalism.NormUnitaryCountingLemmas.N1 := Formalism.NormUnitaryCountingLemmas.gaussian_coefficient_bound_holds

end Formalism.NormUnitaryCountingLemmas.Final
