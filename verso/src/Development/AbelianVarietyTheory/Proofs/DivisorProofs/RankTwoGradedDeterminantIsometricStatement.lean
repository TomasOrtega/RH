import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoGradedDeterminantIsometric
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
Apply `GlobalTheory.VMetric.isometric_grLB_tens_grLB_det` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRankTwoGradedDeterminantIsometric.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.rank_two_graded_determinant_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E : X.Modules) (h : VMetric p E 2)
    (H : h.IsCInf) (fl : Vert.Flag E 2),
    ((VMetric.grLB fl 0 H).tens (VMetric.grLB fl 1 H)).Isometric (VMetric.det H) := by
  first | exact @GlobalTheory.VMetric.isometric_grLB_tens_grLB_det | exact GlobalTheory.VMetric.isometric_grLB_tens_grLB_det | (intros; apply GlobalTheory.VMetric.isometric_grLB_tens_grLB_det <;> assumption)
