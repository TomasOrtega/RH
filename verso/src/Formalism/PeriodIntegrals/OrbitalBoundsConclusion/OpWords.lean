import Mathlib
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OpBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.VanishMain

/- English proof (translation)
The claim follows from `PI.OpWords.opBound_of_vanish PI.OpWords.vanishingOnQuadric`.
-/
theorem operator_words_bound : Formalism.MainNotions.TestSideCounting.OpBound :=
  PI.OpWords.opBound_of_vanish PI.OpWords.vanishingOnQuadric
