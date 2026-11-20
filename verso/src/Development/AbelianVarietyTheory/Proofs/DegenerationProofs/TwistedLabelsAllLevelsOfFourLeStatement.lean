import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedLabelsAllLevelsOfFourLe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Ex.LabelsAllLevels.labels_of_four_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FTwistedLabelsAllLevelsOfFourLe.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.twistedLabels_all_levels_of_four_le : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → (∀ k, 4 ≤ k → Labels A u r M ν' J k) → ∀ k, 0 < k → Labels A u r M ν' J k := by
  first | exact @GlobalTheory.Ex.LabelsAllLevels.labels_of_four_le | exact GlobalTheory.Ex.LabelsAllLevels.labels_of_four_le | (intros; apply GlobalTheory.Ex.LabelsAllLevels.labels_of_four_le <;> assumption)
