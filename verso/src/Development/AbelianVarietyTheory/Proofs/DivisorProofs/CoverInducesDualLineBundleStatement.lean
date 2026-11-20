import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverInducesDualLineBundle
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoverInducesDualLineBundle.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.cover_induces_dual_line_bundle : ∀ (D : D7) (O : Setup D), O.Core → ∀ (R : ℝ) (c : O.s.Comp) (V : Cover (O.var c)) (st : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ) (L : HermLB V.p), V.Induces (lineAdl O R c st 1) L 1 → V.Induces (lineAdl O R c st (-1)) L.dual 1 := by
  first | exact @GlobalTheory.TwoLat.induces_lineAdl_neg | exact GlobalTheory.TwoLat.induces_lineAdl_neg | (intros; apply GlobalTheory.TwoLat.induces_lineAdl_neg <;> assumption)
