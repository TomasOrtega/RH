import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelNefOfAmple
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArithHilbertSamuelNefOfAmple.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.arithHilbertSamuel_nef_of_ample : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → GlobalTheory.Published.ArithHilbertSamuel := by
  first | exact @GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS | exact GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS | (intros; apply GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS <;> assumption)
