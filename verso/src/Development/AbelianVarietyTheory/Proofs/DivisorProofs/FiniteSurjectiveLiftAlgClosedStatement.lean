import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSurjectiveLiftAlgClosed
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagCls.finite_exists_lift_algClosed_point` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteSurjectiveLiftAlgClosed.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.finite_surjective_lift_alg_closed : ∀ (Bg S : Scheme.{0}) (πB : Bg ⟶ S), IsFinite πB → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), x (IsLocalRing.closedPoint K) ∈ Set.range πB → ∃ xb : Sp K ⟶ Bg, xb ≫ πB = x := by
  first | exact @GlobalTheory.FlagCls.finite_exists_lift_algClosed_point | exact GlobalTheory.FlagCls.finite_exists_lift_algClosed_point | (intros; apply GlobalTheory.FlagCls.finite_exists_lift_algClosed_point <;> assumption)
