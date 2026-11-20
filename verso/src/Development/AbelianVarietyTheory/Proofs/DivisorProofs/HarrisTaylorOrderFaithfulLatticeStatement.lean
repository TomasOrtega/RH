import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorOrderFaithfulLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHarrisTaylorOrderFaithfulLattice.lean&line=167#L167)
-/
theorem _root_.GlobalTheory.T.harrisTaylor_order_faithful_lattice : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O), (∀ y : D.La, x • y = 0) → x = 0 := by
  first | exact @GlobalTheory.HTFaith.faithful | exact GlobalTheory.HTFaith.faithful | (intros; apply GlobalTheory.HTFaith.faithful <;> assumption)
