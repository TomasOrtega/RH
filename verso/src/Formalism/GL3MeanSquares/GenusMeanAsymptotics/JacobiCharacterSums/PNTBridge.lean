import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTFinal
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqFinal
import Formalism.GL3MeanSquares.PrimePairOfPrimeNumberTheoremInProgressions

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem pnt_progressions_relative_iff : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.PNTAPRelW ↔ Formalism.HermitianLattices.PrimeNumberTheoremConsequences.PNTAPRelW := Iff.rfl

/- English proof (translation)
The claim follows from `pnt_progressions_relative_iff.1 pnt_progressions_relative_weak_holds`.
-/
theorem pnt_progressions_relative_weak : Formalism.HermitianLattices.PrimeNumberTheoremConsequences.PNTAPRelW := pnt_progressions_relative_iff.1 pnt_progressions_relative_weak_holds

end Formalism.HermitianLattices.Ext.PrimesInProgressions
