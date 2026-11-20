import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwoGoodSectionsNearClosedPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZJ.Core.Law.six_of_few` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsTwoGoodSectionsNearClosedPoint.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.companionTheory_om_of_tests_torsionSections : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), C.HasTests → T.BTest L → C.TorsSec n → T.Few n → L.CompanionTheory (T.Om L) := by
  first | exact @GlobalTheory.ZJ.Core.Law.six_of_few | exact GlobalTheory.ZJ.Core.Law.six_of_few | (intros; apply GlobalTheory.ZJ.Core.Law.six_of_few <;> assumption)
