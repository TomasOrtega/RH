import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.KsetSubset

open Matrix
open PI.UpqRep (UJset Kset IsKFin IsKStableOn)

namespace GlobalTheory.CompanionTheory.KFinStab

/- English proof (citation)
Apply `UpperTheory.Reformulated.B.Gc1.kFinStab` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FIntegralCasts%2FCapelliIdentities%2FKsetSubset.lean&line=12#L12)
-/
theorem kFinStab : CompanionTheory.D.DSIC.KFinStab :=
  _root_.UpperTheory.Reformulated.B.Gc1.kFinStab

end GlobalTheory.CompanionTheory.KFinStab
