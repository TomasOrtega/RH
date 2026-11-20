import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
import Formalism.LatticeRigidity.HeightMin
import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
import Formalism.GelfandTransference.HadamardGelfand.Transference
import Mathlib
import Formalism.LatticeRigidity.HeightMinimum.BlockEquationHolds
import Formalism.LatticeRigidity.HeightMinimum.ChebyshevLeadingCoeffHolds
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
import Formalism.LatticeRigidity.HeightMinimum.OneLeProdOfInt

namespace Formalism.SA.Final

/- English proof (translation)
The claim follows from `Formalism.SA.P.smoothedSumBound`.
-/
theorem boxSum : Formalism.SA.C.BoxSum := Formalism.SA.P.smoothedSumBound

end Formalism.SA.Final
