import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorLowerBoundOfPlaceBoundWitt
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwU.LowGen.cofactor_lower_bound_of_place_bound_witt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FCofactorLowerBoundOfPlaceBoundWitt.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.lowAt_of_placeCofactorValuationLowerBound : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (j : ℕ) (v : X.Pl) (g : ℝ), MvPowerSeries.constantCoeff Y.be = 0 → IsPlaceCofactorValuationLowerBound X Y.be j v g → Y.LowAt j v g := by
  first | exact @GlobalTheory.TwU.LowGen.cofactor_lower_bound_of_place_bound_witt | exact GlobalTheory.TwU.LowGen.cofactor_lower_bound_of_place_bound_witt | (intros; apply GlobalTheory.TwU.LowGen.cofactor_lower_bound_of_place_bound_witt <;> assumption)
