import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundlePositivityPreservedIsometric
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHermitianLineBundlePositivityPreservedIsometric.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L M : HermLB p, L.Isometric M → (L.SemiPos D → M.SemiPos D) ∧ (L.IsNef D → M.IsNef D) ∧ (HtNef L D → HtNef M D) ∧ (∀ a, L.IsSelfInter a → M.IsSelfInter a) ∧ (IsAmpleLB L.B → IsAmpleLB M.B) := by
  first | exact @GlobalTheory.HSNef.isometric_keeps | exact GlobalTheory.HSNef.isometric_keeps | (intros; apply GlobalTheory.HSNef.isometric_keeps <;> assumption)
