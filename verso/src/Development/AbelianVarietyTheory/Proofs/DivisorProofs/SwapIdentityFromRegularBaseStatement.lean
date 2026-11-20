import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapIdentityFromRegularBase
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovTest.swap2_of_swapRegular` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSwapIdentityFromRegularBase.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.swap_identity_from_regular_base : ArCalc → RegularAlteration → GdegPull → ∀ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, SwapReg G → Swap2 G := by
  first | exact @GlobalTheory.CovTest.swap2_of_swapRegular | exact GlobalTheory.CovTest.swap2_of_swapRegular | (intros; apply GlobalTheory.CovTest.swap2_of_swapRegular <;> assumption)
