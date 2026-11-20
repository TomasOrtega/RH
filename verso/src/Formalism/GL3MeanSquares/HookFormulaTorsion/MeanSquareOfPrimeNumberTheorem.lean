import Mathlib
import Formalism.GL3MeanSquares.PrimePairOfPrimeNumberTheoremInProgressions
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqFinal
import Formalism.GL3MeanSquares.HookFormulaTorsion.PrimePairOfBoxAndWeakMeanSquareHypotheses
import Formalism.GL3MeanSquares.HookFormulaTorsion.BoxCountOfZeroDensity
import Formalism.GL3MeanSquares.HookFormulaTorsion.BoxCountAllStatement

noncomputable section

namespace Formalism.HermitianLattices.PrimeNumberTheoremConsequences

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem PNTAPRelW_iff_ext : PNTAPRelW ↔ Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.PNTAPRelW := Iff.rfl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem mean_square_of_prime_number_theorem : MeanSquareFromPNT := fun hP =>
  Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.mean_square_of_pnt_progressions (PNTAPRelW_iff_ext.1 hP)

end Formalism.HermitianLattices.PrimeNumberTheoremConsequences
