import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffExistsSmallSectionDiffe
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HSNef.le_iff_exists_smallSec` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHermLBLeBySmallSectionIffExistsSmallSectionDiffe.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.hermLBLeBySmallSection_iff_exists_smallSection_difference : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B : HermLB p, Le B A ↔ ∃ s ∈ (A.tens B.dual).smallSec, s ≠ 0 := by
  first | exact @GlobalTheory.HSNef.le_iff_exists_smallSec | exact GlobalTheory.HSNef.le_iff_exists_smallSec | (intros; apply GlobalTheory.HSNef.le_iff_exists_smallSec <;> assumption)
