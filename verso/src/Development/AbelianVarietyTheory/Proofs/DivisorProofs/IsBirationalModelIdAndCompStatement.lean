import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelIdAndComp
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsBirationalModelIdAndComp.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.isBirationalModel_id_and_comp : ∀ (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (π : Y ⟶ X) (π' : Z ⟶ Y) (φ : X.functionField →+* Y.functionField) (φ' : Y.functionField →+* Z.functionField), IsModel (𝟙 X) (RingHom.id _) ∧ (IsModel π φ → IsModel π' φ' → IsModel (π' ≫ π) (φ'.comp φ)) := by
  first | exact @GlobalTheory.HSNef.isModel_id_and_comp | exact GlobalTheory.HSNef.isModel_id_and_comp | (intros; apply GlobalTheory.HSNef.isModel_id_and_comp <;> assumption)
