import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIntersectionNumberGroundFieldChange
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GroundFieldChange.interNum_fieldChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLineBundleIntersectionNumberGroundFieldChange.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange : ∀ (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0}) [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (G : Z.Modules) {ι : Type} [Fintype ι] (L : ι → LB Z), interNum κ G L = (Module.finrank κ κ' : ℤ) * interNum κ' G L := by
  first | exact @GlobalTheory.GroundFieldChange.interNum_fieldChange | exact GlobalTheory.GroundFieldChange.interNum_fieldChange | (intros; apply GlobalTheory.GroundFieldChange.interNum_fieldChange <;> assumption)
