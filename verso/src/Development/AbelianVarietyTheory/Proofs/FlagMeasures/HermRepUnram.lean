import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianFormRepresentsTotallyPositiveStatement

namespace GlobalTheory

/- English proof (translation)
The claim follows from `GlobalTheory.T.binaryHermitianForm_represents_totallyPositive`.
-/
theorem hermRepUnram : Formalism.HermitianLattices.Ext.L3.HermRepUnram := GlobalTheory.T.binaryHermitianForm_represents_totallyPositive

instance : Fact (Formalism.HermitianLattices.Ext.L3.HermRepUnram) := ⟨hermRepUnram⟩

end GlobalTheory
