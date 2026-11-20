import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousLineBaseDifference
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovTest.SwapLine.onLine_sub_onBase_factor` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHomogeneousLineBaseDifference.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.homogeneous_line_base_difference : ∀ (d : ℕ) (a b : ℤ), ∃ K : MvPolynomial (Fin 5) ℝ, K.IsHomogeneous d ∧
    onLine d a b - onBase d a b = (X 0 - X 4) * (X 0 - X 3) * K := by
  first | exact @GlobalTheory.CovTest.SwapLine.onLine_sub_onBase_factor | exact GlobalTheory.CovTest.SwapLine.onLine_sub_onBase_factor | (intros; apply GlobalTheory.CovTest.SwapLine.onLine_sub_onBase_factor <;> assumption)
