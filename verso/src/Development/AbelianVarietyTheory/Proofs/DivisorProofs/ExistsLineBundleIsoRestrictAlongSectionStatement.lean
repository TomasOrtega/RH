import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoRestrictAlongSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitImports
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IsoRes.exists_iso_restrict` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLineBundleIsoRestrictAlongSection.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.exists_lineBundleIso_restrict_along_section : ∀ {XG XT Pb : Scheme.{0}} {LG : LB XG} {LT : LB XT} (hG : LG.IsLB) (hT : LT.IsLB) {c : Pb ⟶ XG} {g : Pb ⟶ XT} {gi : XT ⟶ Pb} (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) (hw₀ : w₀.IsGen), ∃ w : LB.Iso LT (LG.pull (gi ≫ c)), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ XT) (z : Z) (j : LG.ι) (k : LT.ι), gw w r z j k = gw w₀ (r ≫ gi) z j (fun _ => k) := by
  first | exact @GlobalTheory.IsoRes.exists_iso_restrict | exact GlobalTheory.IsoRes.exists_iso_restrict | (intros; apply GlobalTheory.IsoRes.exists_iso_restrict <;> assumption)
