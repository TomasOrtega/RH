import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeVandermondeSum
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArithmeticDegreeVandermondeSum.lean&line=194#L194)
-/
theorem _root_.GlobalTheory.T.arithmetic_degree_vandermonde_sum : Hypotheses2 → HypothesesH → RegularAlteration → OnObj fun D O _ _ _ _ => ∀ R : ℝ, 2 ≤ R → O.Y.arMix ∅ R 1 (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau O.Y.N (lamA D.what₂.Tau O.Y.N O.Y.j ^ (dimGr D.what₂.Tau O.Y.N O.Y.j - 1) * (fibPt D.what₂.Tau O.Y.N O.Y.j - vdmCl D.what₂.Tau O.Y.N O.Y.j))) = O.Y.arDeg ∅ R ((∑ τ, (pSum τ 2 : Pol D.what₂.Tau O.Y.N)) * (lamA D.what₂.Tau O.Y.N O.Y.j ^ (dimGr D.what₂.Tau O.Y.N O.Y.j - 1) * (fibPt D.what₂.Tau O.Y.N O.Y.j - vdmCl D.what₂.Tau O.Y.N O.Y.j))) := by
  first | exact @GlobalTheory.EigWholeDR.whole_eq_eig_DR | exact GlobalTheory.EigWholeDR.whole_eq_eig_DR | (intros; apply GlobalTheory.EigWholeDR.whole_eq_eig_DR <;> assumption)
