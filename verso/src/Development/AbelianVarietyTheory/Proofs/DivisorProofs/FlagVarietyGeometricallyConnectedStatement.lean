import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagQ.geometricallyConnected_genericFibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagVarietyGeometricallyConnected.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.flag_variety_geometrically_connected : ∀ (ι : Type) [Fintype ι] (N : ℕ), GeometricallyConnected (pullback.snd (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ))) := by
  first | exact @GlobalTheory.FlagQ.geometricallyConnected_genericFibre | exact GlobalTheory.FlagQ.geometricallyConnected_genericFibre | (intros; apply GlobalTheory.FlagQ.geometricallyConnected_genericFibre <;> assumption)
