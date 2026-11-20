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
A detailed English derivation is pending.
-/
theorem reduction_lemma_zero : GramDeterminantQuotientMetric := gram_determinant_quotient_metric
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaRb : LemmaRb := reduction_lemma_second
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem specDet : SpecDet := spectral_determinant_formula
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepB : StepB := reduction_second_step
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepA : StepA := reduction_first_step
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepC : StepC := reduction_third_step

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem interlace : Formalism.LatticeIndexTer.Interlace := Formalism.LatticeIndexTer.sumInterlacedBound

end Formalism.DivisionValues
