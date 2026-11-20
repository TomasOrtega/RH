import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSymmetricImpliesSwapFlag
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovTest.SwapFlProof.swapFl_of_swap2` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSwapSymmetricImpliesSwapFlag.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.swap_symmetric_implies_swap_flag : ArCalc → ∀ G, Homog G → Swap2 G → SwapFl G := by
  first | exact @GlobalTheory.CovTest.SwapFlProof.swapFl_of_swap2 | exact GlobalTheory.CovTest.SwapFlProof.swapFl_of_swap2 | (intros; apply GlobalTheory.CovTest.SwapFlProof.swapFl_of_swap2 <;> assumption)
