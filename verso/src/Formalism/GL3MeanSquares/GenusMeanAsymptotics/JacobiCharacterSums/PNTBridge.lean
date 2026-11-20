import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTFinal
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqFinal
import Formalism.GL3MeanSquares.PrimePairOfPrimeNumberTheoremInProgressions

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem pnt_progressions_relative_iff : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.PNTAPRelW ↔ Formalism.HermitianLattices.PrimeNumberTheoremConsequences.PNTAPRelW := Iff.rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pnt_progressions_relative_weak : Formalism.HermitianLattices.PrimeNumberTheoremConsequences.PNTAPRelW := pnt_progressions_relative_iff.1 pnt_progressions_relative_weak_holds

end Formalism.HermitianLattices.Ext.PrimesInProgressions
