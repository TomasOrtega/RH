import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingEverywhereOfRegularAlteration
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
Apply `GlobalTheory.TwoLat.Gen.vanishOn_of_regFlagged` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVanishingEverywhereOfRegularAlteration.lean&line=317#L317)
-/
theorem _root_.GlobalTheory.T.vanishing_everywhere_of_regular_alteration : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → VanishOn RegFlagged → VanishOn fun _ _ _ _ _ _ => True := by
  first | exact @GlobalTheory.TwoLat.Gen.vanishOn_of_regFlagged | exact GlobalTheory.TwoLat.Gen.vanishOn_of_regFlagged | (intros; apply GlobalTheory.TwoLat.Gen.vanishOn_of_regFlagged <;> assumption)
