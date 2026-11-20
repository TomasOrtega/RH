import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSectionProjectiveOverField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsClosedImageSectionProjectiveOverField.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.isClosed_image_section_projective_over_field : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z : Sp K ⟶ X), IsProjOver q → z ≫ q = 𝟙 _ → IsClosed ({z (IsLocalRing.closedPoint K)} : Set X) := by
  first | exact @GlobalTheory.secClosed_closedPoint | exact GlobalTheory.secClosed_closedPoint | (intros; apply GlobalTheory.secClosed_closedPoint <;> assumption)
