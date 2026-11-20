import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Ex.brFam | exact GlobalTheory.Ex.brFam | (intros; apply GlobalTheory.Ex.brFam <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.families_values_correspond : Laws → Laws2 → BrFamSt := by
  first | exact @GlobalTheory.Ex.brFam | exact GlobalTheory.Ex.brFam | (intros; apply GlobalTheory.Ex.brFam <;> assumption)
