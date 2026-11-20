import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalAdaptedSections
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLocalAdaptedSections.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.exists_local_adapted_sections : ∀ (Y : Scheme.{0}) (N : Y.Modules) (r : ℕ) (fl : Vert.Flag N r) (p : Y) (U : Y.Opens), p ∈ U → ∃ (W : Y.Opens) (s : Fin r → Γ(N, W)), W ≤ U ∧ p ∈ W ∧ Adapted fl s := by
  first | exact @GlobalTheory.FlagCls.exists_adapted | exact GlobalTheory.FlagCls.exists_adapted | (intros; apply GlobalTheory.FlagCls.exists_adapted <;> assumption)
