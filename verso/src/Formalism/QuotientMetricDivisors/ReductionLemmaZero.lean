import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjTransposeEqOfPosDef
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaSecond
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SpecDet
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionSecondStep
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.VwEqZeroOfNotMem
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionThirdStepMean
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.BoundsSum
import Formalism.LogFactorialIndices.SignedSubspaceIndex.SumInterlacedBoundFails
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TheoremFSharp

namespace Formalism.DivisionValues

/- English proof (translation)
The claim follows from `gram_determinant_quotient_metric`.
-/
theorem reduction_lemma_zero : GramDeterminantQuotientMetric := gram_determinant_quotient_metric
/- English proof (translation)
The claim follows from `reduction_lemma_second`.
-/
theorem lemmaRb : LemmaRb := reduction_lemma_second
/- English proof (translation)
The claim follows from `spectral_determinant_formula`.
-/
theorem specDet : SpecDet := spectral_determinant_formula
/- English proof (translation)
The claim follows from `reduction_second_step`.
-/
theorem stepB : StepB := reduction_second_step
/- English proof (translation)
The claim follows from `reduction_first_step`.
-/
theorem stepA : StepA := reduction_first_step
/- English proof (translation)
The claim follows from `reduction_third_step`.
-/
theorem stepC : StepC := reduction_third_step

/- English proof (translation)
The claim follows from `Formalism.LatticeIndexTer.sumInterlacedBound`.
-/
theorem interlace : Formalism.LatticeIndexTer.Interlace := Formalism.LatticeIndexTer.sumInterlacedBound

end Formalism.DivisionValues
