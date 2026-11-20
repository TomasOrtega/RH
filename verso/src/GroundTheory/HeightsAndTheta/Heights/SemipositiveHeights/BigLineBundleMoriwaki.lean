import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

/- English proof (translation)
The claim follows from `HilbertSamuel.ArithmeticVolumeBig.arithmeticVolumeBig_smoothFibre (HilbertSamuel.ArithmeticVolumeBig.of_moriwakiBig_only hM)`.
-/
theorem BigLineBundleMoriwaki.of_moriwakiBig (hM : MoriwakiBigStatement) : ArithmeticVolumeLowerBound :=
  HilbertSamuel.ArithmeticVolumeBig.arithmeticVolumeBig_smoothFibre (HilbertSamuel.ArithmeticVolumeBig.of_moriwakiBig_only hM)

end GroundTheory.Heights₂.Heights.ForSecondHalf
