import Mathlib
import Formalism.HermitianLattices.StatementMass
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LiStatOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianRepresents

namespace GlobalTheory.Mass

/- English proof (translation)
The claim follows from `Formalism.HermitianLattices.Ext.L3.siegelMassRatio_of_LI binary_hermitian_represents Formalism.HermitianLattices.Ext.L3.liStat`.
-/
theorem siegelMassRatio_holds : Formalism.HermitianLatticesTheory.SiegelMassRatio :=
  Formalism.HermitianLattices.Ext.L3.siegelMassRatio_of_LI binary_hermitian_represents Formalism.HermitianLattices.Ext.L3.liStat

end GlobalTheory.Mass
