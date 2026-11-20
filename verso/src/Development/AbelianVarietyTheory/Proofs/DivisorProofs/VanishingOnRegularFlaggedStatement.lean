import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSectionLiftsMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineBundleInducedArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleMetricSetupStatement
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TwoLat
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwoLat.vanishOn_regFlagged` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVanishingOnRegularFlagged.lean&line=177#L177)
-/
theorem _root_.GlobalTheory.T.vanishing_on_regular_flagged : GlobalTheory.CovTop.Hypotheses2 → VanishOn RegFlagged := by
  first | exact @GlobalTheory.TwoLat.vanishOn_regFlagged | exact GlobalTheory.TwoLat.vanishOn_regFlagged | (intros; apply GlobalTheory.TwoLat.vanishOn_regFlagged <;> assumption)
