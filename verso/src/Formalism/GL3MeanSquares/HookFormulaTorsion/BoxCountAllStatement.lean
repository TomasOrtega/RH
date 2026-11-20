import Mathlib
import Formalism.GL3MeanSquares.BoxCountAll
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountOut

noncomputable section

namespace Formalism.HermitianLattices.BoxCountUnconditional

/- English proof (translation)
The claim follows from `Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.boxCountHyp_outright`.
-/
theorem boxCountAll_statement : BoxCountAll := Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.boxCountHyp_outright

end Formalism.HermitianLattices.BoxCountUnconditional
