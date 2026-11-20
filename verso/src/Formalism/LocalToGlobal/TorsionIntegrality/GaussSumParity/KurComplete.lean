import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExistsUnitFactorizationBounded
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.IntegralPartAtVariable

namespace Formalism.L2.Th1.D

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ringAFacts : RingAFacts := ring_a_facts
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kurIntegers : KurIntegers := KurIntegers_of ringAFacts
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kurUnram : KurUnram := KurUnram_of kurIntegers
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kurRoots : KurRoots := unramified_completion_roots
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kurComplete : KurComplete := unramified_completion_complete
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frobAIsom : FrobAIsom := FrobAIsom_of ringAFacts
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kurFrob : KurFrob := KurFrob_of frobA frobAIsom kurIntegers kurUnram
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fOfBetaHyp : FOfBetaHyp := f_of_beta_hypotheses

end Formalism.L2.Th1.D
