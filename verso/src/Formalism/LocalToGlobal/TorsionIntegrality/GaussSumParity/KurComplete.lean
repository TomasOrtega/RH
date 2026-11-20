import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExistsUnitFactorizationBounded
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.IntegralPartAtVariable

namespace Formalism.L2.Th1.D

/- English proof (translation)
The claim follows from `ring_a_facts`.
-/
theorem ringAFacts : RingAFacts := ring_a_facts
/- English proof (translation)
The claim follows from `KurIntegers_of ringAFacts`.
-/
theorem kurIntegers : KurIntegers := KurIntegers_of ringAFacts
/- English proof (translation)
The claim follows from `KurUnram_of kurIntegers`.
-/
theorem kurUnram : KurUnram := KurUnram_of kurIntegers
/- English proof (translation)
The claim follows from `unramified_completion_roots`.
-/
theorem kurRoots : KurRoots := unramified_completion_roots
/- English proof (translation)
The claim follows from `unramified_completion_complete`.
-/
theorem kurComplete : KurComplete := unramified_completion_complete
/- English proof (translation)
The claim follows from `FrobAIsom_of ringAFacts`.
-/
theorem frobAIsom : FrobAIsom := FrobAIsom_of ringAFacts
/- English proof (translation)
The claim follows from `KurFrob_of frobA frobAIsom kurIntegers kurUnram`.
-/
theorem kurFrob : KurFrob := KurFrob_of frobA frobAIsom kurIntegers kurUnram
/- English proof (translation)
The claim follows from `f_of_beta_hypotheses`.
-/
theorem fOfBetaHyp : FOfBetaHyp := f_of_beta_hypotheses

end Formalism.L2.Th1.D
