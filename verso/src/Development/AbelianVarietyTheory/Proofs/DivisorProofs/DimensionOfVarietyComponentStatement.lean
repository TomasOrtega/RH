import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfVarietyComponent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDimensionOfVarietyComponent.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.dimension_of_variety_component : ∀ (D : D7) (O : Setup D), O.Core → ∀ c : O.s.Comp,
    dimGr D.what₂.Tau O.N O.j + ∑ σ : D.host.E →+* ℂ, O.S.Dw.mult σ * (O.S.Dw.mult σ - 1) / 2 = (O.var c).dim := by
  first | exact @GlobalTheory.FlagEigDim.dim_eq_dimGr_add_sum | exact GlobalTheory.FlagEigDim.dim_eq_dimGr_add_sum | (intros; apply GlobalTheory.FlagEigDim.dim_eq_dimGr_add_sum <;> assumption)
