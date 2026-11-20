import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithmeticCoverOverModification
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsArithmeticCoverOverModification.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.exists_arithmeticCover_over_modification : ∀ (k : Type) [CommRing k] (X X' Y : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral Y] (p : X ⟶ Sp k) (D E : ℕ) (ρ : X' ⟶ X) (π : Y ⟶ X), IsArithVar p D → IsArithVar (ρ ≫ p) D → IsArithVar (π ≫ p) E → ρ (genericPoint X') = genericPoint X → ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (g : Y' ⟶ Y) (π' : Y' ⟶ X'), π' ≫ ρ = g ≫ π ∧ IsArithVar (g ≫ π ≫ p) E ∧ g (genericPoint Y') = genericPoint Y ∧ g.residueDegree (genericPoint Y') ≠ 0 := by
  first | exact @GlobalTheory.CoverLift.exists_cover_over_modification | exact GlobalTheory.CoverLift.exists_cover_over_modification | (intros; apply GlobalTheory.CoverLift.exists_cover_over_modification <;> assumption)
