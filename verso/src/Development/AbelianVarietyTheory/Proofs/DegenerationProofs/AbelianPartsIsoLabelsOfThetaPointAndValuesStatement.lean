import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartsIsoLabelsOfThetaPointAndValues
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Ex.AbPartIso.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FAbelianPartsIsoLabelsOfThetaPointAndValues.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.abelianPartsIsoLabels_of_thetaPoint_and_values : Laws → ThetaPtDeterminesSt → BrUthSt → UrCSt := by
  first | exact @GlobalTheory.Ex.AbPartIso.main | exact GlobalTheory.Ex.AbPartIso.main | (intros; apply GlobalTheory.Ex.AbPartIso.main <;> assumption)
