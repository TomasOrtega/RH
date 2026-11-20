import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyDivisorDimension
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
Apply `GlobalTheory.CodimOneDim.topologicalKrullDim_eq_of_coheight_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArithmeticVarietyDivisorDimension.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.arithmetic_variety_divisor_dimension : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z],
    Order.coheight (i (genericPoint Z)) = 1 → topologicalKrullDim Z = D := by
  first | exact @GlobalTheory.CodimOneDim.topologicalKrullDim_eq_of_coheight_eq_one | exact GlobalTheory.CodimOneDim.topologicalKrullDim_eq_of_coheight_eq_one | (intros; apply GlobalTheory.CodimOneDim.topologicalKrullDim_eq_of_coheight_eq_one <;> assumption)
